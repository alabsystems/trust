//! Fixed live-kernel observation roles. These descriptors are neither immutable
//! source inputs nor writable scratch; each read has a bounded offset/length.
use super::{Error, Filter, JEQ, JGE, LD};

fn equal64(f: &mut Filter, argument: u32, value: u32) -> Result<(), Error> {
    f.push(LD, 0, 0, 20 + argument * 8)?;
    f.push(JEQ, 1, 0, 0)?;
    f.deny()?;
    f.arg(argument)?;
    f.push(JEQ, 1, 0, value)?;
    f.deny()
}

pub(super) fn pread(f: &mut Filter, ordinary: &[u32]) -> Result<(), Error> {
    f.arg(0)?;
    let statm = f.len;
    f.push(JEQ, 0, 0, 6)?;
    let meminfo = f.len;
    f.push(JEQ, 0, 0, 7)?;
    f.fds(0, ordinary, Some(8))?;
    f.allow()?;
    let special = f.len;
    for branch in [statm, meminfo] {
        f.instructions[branch].jt = u8::try_from(special - branch - 1)
            .map_err(|_| Error::Contract("resource read branch"))?;
    }
    equal64(f, 3, 0)?;
    f.push(LD, 0, 0, 36)?; // pread count's high word
    f.push(JEQ, 1, 0, 0)?;
    f.deny()?;
    f.arg(2)?;
    f.push(JGE, 0, 1, 8193)?;
    f.deny()
}

pub(super) fn exclude(f: &mut Filter, argument: u32) -> Result<(), Error> {
    f.arg(argument)?;
    for descriptor in [6, 7] {
        f.push(JEQ, 0, 1, descriptor)?;
        f.deny()?;
    }
    Ok(())
}

pub(super) fn append(f: &mut Filter) -> Result<(), Error> {
    f.rule(libc::SYS_getrusage, |f| equal64(f, 0, libc::RUSAGE_SELF as u32))
}

#[cfg(test)]
mod tests;
