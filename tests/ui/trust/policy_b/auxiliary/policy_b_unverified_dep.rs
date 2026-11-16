//@ compile-flags: --crate-type=rlib -Ztrust-verify=off -Zalways-encode-mir
//@ no-prefer-dynamic
//! A dependency compiled with verification OFF, the way Targo compiles every
//! dependency unit. `deref_raw` dereferences an arbitrary address — nothing here
//! is checked by Trust. It exists so the caller fixture can prove that a NON-std
//! absent callee stays fatal under policy B.
#![feature(allocator_api)]
#[inline(always)]
pub fn deref_raw(p: *const u32) -> u32 {
    unsafe { *p }
}

/// Refuted 2026-09-16 (type-walk lens): a plain function that panics on one
/// input. NOTHING here is checked by Trust, so a caller that reaches it must be
/// refused even when the fold's representative row is a tolerated sysroot callee.
pub fn boom(x: u8) -> u8 {
    if x == 3 {
        panic!("DEP USER PANIC (unverified crate)")
    }
    x
}

/// A `FromStr` impl in an unverified crate: `str::parse::<P>` is a SYSROOT callee
/// whose type argument reaches this body.
pub struct P;
impl std::str::FromStr for P {
    type Err = ();
    fn from_str(s: &str) -> Result<P, ()> {
        if s == "3" {
            panic!("DEP FROMSTR PANIC (unverified crate)")
        }
        Ok(P)
    }
}

/// A `Drop` impl in an unverified crate, reached through `Vec<Bomb>`'s drop glue.
/// Its derived `Debug` (also unverified code) is what `<Result<(), Bomb> as
/// Termination>::report` runs on `Err` — see `entry_termination_dispatch_reported.rs`.
#[derive(Debug)]
pub struct Bomb(pub u8);
impl Drop for Bomb {
    fn drop(&mut self) {
        if self.0 == 3 {
            panic!("DEP DROP PANIC (unverified crate)")
        }
    }
}

/// Refuted 2026-09-16 (fold-mask lens, resumed): a `core::fmt::Write` impl in an
/// unverified crate. A call `<Buf as fmt::Write>::write_str(..)` is spelled with the
/// TRAIT item (`core::fmt::Write::write_str`) and this type in `Self`; the fold
/// mask's fmt-machinery exemption used to cover it.
pub struct Buf(pub u8);
impl std::fmt::Write for Buf {
    fn write_str(&mut self, s: &str) -> std::fmt::Result {
        if s == "3" {
            panic!("DEP FMT::WRITE PANIC (unverified crate)")
        }
        self.0 = self.0.wrapping_add(s.len() as u8);
        Ok(())
    }
}

/// Refuted 2026-09-16 (allocator lens, resumed): an `Allocator` in an unverified
/// crate, carried as `Box<T, DepAlloc>`'s allocator PARAMETER — no
/// `#[global_allocator]` involved, so the global-alloc contract is not the
/// premise; the container's own drop calls this `deallocate`.
pub struct DepAlloc;
unsafe impl std::alloc::Allocator for DepAlloc {
    fn allocate(
        &self,
        layout: std::alloc::Layout,
    ) -> Result<std::ptr::NonNull<[u8]>, std::alloc::AllocError> {
        std::alloc::Global.allocate(layout)
    }
    unsafe fn deallocate(&self, ptr: std::ptr::NonNull<u8>, layout: std::alloc::Layout) {
        if layout.size() == 4 {
            panic!("DEP DEALLOCATE PANIC (unverified crate)")
        }
        unsafe { std::alloc::Global.deallocate(ptr, layout) }
    }
}
