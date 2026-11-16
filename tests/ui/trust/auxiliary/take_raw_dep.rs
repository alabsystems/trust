//@ compile-flags: --crate-type=rlib -Ztrust-verify=off -Zalways-encode-mir
//@ no-prefer-dynamic
//! A verify-off dependency whose one export takes a reference to a RAW POINTER,
//! `&*const u8` — the pointee that itself spells `Ty::Ptr`. It exists so the
//! caller fixture can pin that signing this parameter is REFUSED.
pub fn take_raw(p: &*const u8) -> u8 {
    unsafe { **p }
}
