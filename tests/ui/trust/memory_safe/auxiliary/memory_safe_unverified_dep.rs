//@ compile-flags: --crate-type=rlib -Ztrust-verify=off -Zalways-encode-mir
//@ no-prefer-dynamic
//! A dependency compiled with verification OFF, the way Targo compiles every
//! dependency unit. Every function here is a SAFE signature over unchecked
//! behaviour, and nothing here is checked by Trust:
//! `deref_raw` reads an arbitrary address, `get` and `never` reach
//! `unreachable_unchecked`, the second behind a `-> !` signature, and so does
//! `Boom`'s `Default` — a trait impl a std routine calls on the caller's behalf
//! (`Option::<Boom>::unwrap_or_default`). `SCALE` is the one item a memory-safe
//! caller may use freely: a constant, not a call.
#[inline(always)]
pub fn deref_raw(p: *const u32) -> u32 {
    unsafe { *p }
}

pub fn get() -> u32 {
    unsafe { core::hint::unreachable_unchecked() }
}

pub fn never() -> ! {
    unsafe { core::hint::unreachable_unchecked() }
}

pub struct Boom(pub u32);

impl Default for Boom {
    fn default() -> Self {
        unsafe { core::hint::unreachable_unchecked() }
    }
}

pub const SCALE: u32 = 1000;

/// Dependency code a caller's DROP runs rather than calls: `Crash`'s destructor
/// (through a type parameter's drop glue or a `Box<dyn Any>`) and `Sink`'s
/// `Write::write` (through the flush in `BufWriter<Sink>`'s foundational destructor).
pub struct Crash(pub u32);

impl Drop for Crash {
    fn drop(&mut self) {
        unsafe { core::hint::unreachable_unchecked() }
    }
}

pub struct Sink;

impl std::io::Write for Sink {
    fn write(&mut self, _buf: &[u8]) -> std::io::Result<usize> {
        unsafe { core::hint::unreachable_unchecked() }
    }

    fn flush(&mut self) -> std::io::Result<()> {
        Ok(())
    }
}
