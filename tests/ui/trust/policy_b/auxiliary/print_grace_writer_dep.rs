//@ compile-flags: --crate-type=rlib -Ztrust-verify=off
//@ no-prefer-dynamic
//! A dependency compiled with verification OFF, the way Targo compiles every
//! dependency unit (`print_grace_drop_glue_reaches_foreign_code.rs`): an
//! `io::Write` sink with no destructor of its own, whose `write` stores through a
//! null pointer. A std owner's destructor reaches it (`BufWriter<Sink>` flushes its
//! buffer through `Sink::write`).

pub struct Sink;

impl std::io::Write for Sink {
    fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
        // SAFETY: none — this is the unverified dependency's undefined behaviour.
        unsafe { core::ptr::write_volatile(core::ptr::null_mut::<usize>(), buf.len()) }
        Ok(buf.len())
    }

    fn flush(&mut self) -> std::io::Result<()> {
        Ok(())
    }
}
