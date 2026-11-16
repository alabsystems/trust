//! Fixed-channel native bootstrap/receipt IO. B1 framing remains B1's codec.
use std::io::ErrorKind;

use trust_process_isolation::{Budget, Charge};

use super::{charge, check, contract};
use crate::{Error, system};

fn wait(event: i16, budget: Option<&Budget>) -> Result<(), Error> {
    if let Some(b) = budget {
        charge(b, Charge { work: 64, ..Charge::default() })?;
    }
    let mut poll = libc::pollfd { fd: 3, events: event, revents: 0 };
    let timeout = libc::timespec { tv_sec: 0, tv_nsec: 1_000_000 };
    // SAFETY: initialized complete stack records and a finite wait; FD3 was
    // authenticated before fixed startup, and protected after confinement.
    let n = unsafe { libc::ppoll(&mut poll, 1, &timeout, std::ptr::null()) };
    if let Some(b) = budget {
        check(b)?;
    }
    if n < 0 && std::io::Error::last_os_error().kind() != ErrorKind::Interrupted {
        return Err(system("native fixed-channel poll"));
    }
    if poll.revents & libc::POLLNVAL != 0 {
        return Err(Error::Contract("native fixed channel invalid"));
    }
    Ok(())
}
fn read(mut bytes: &mut [u8], budget: Option<&Budget>) -> Result<(), Error> {
    while !bytes.is_empty() {
        let count = bytes.len().min(4096);
        if let Some(b) = budget {
            charge(b, Charge { work: count as u64, ..Charge::default() })?;
        }
        // SAFETY: exact writable bounded destination; only fixed FD3 is used.
        let n = unsafe { libc::read(3, bytes.as_mut_ptr().cast(), count) };
        let error = if n < 0 { Some(std::io::Error::last_os_error()) } else { None };
        if let Some(b) = budget {
            check(b)?;
        }
        match (n, error) {
            (n, None) if n > 0 && n as usize <= count => bytes = &mut bytes[n as usize..],
            (_, Some(error)) if error.kind() == ErrorKind::WouldBlock => {
                wait(libc::POLLIN, budget)?
            }
            (_, Some(error)) if error.kind() == ErrorKind::Interrupted => {}
            _ => return Err(Error::Contract("native fixed-channel EOF/read")),
        }
    }
    Ok(())
}
/// Only one acknowledged byte and the fixed112byte grant can be read before a
/// local meter exists. Parent prepaid startup and independent owned monitoring
/// are mandatory; this function cannot allocate or read an arbitrary payload.
pub(super) fn startup() -> Result<[u8; super::grant::WIRE], Error> {
    let mut ack = [0];
    read(&mut ack, None)?;
    if ack != *b"C" {
        return Err(Error::Contract("native post-exec acknowledgement"));
    }
    let mut grant = [0; super::grant::WIRE];
    read(&mut grant, None)?;
    Ok(grant)
}
pub(super) fn read_exact(bytes: &mut [u8], b: &Budget) -> Result<(), Error> {
    let result = read(bytes, Some(b));
    if result.is_err() {
        b.refuse(trust_process_isolation::Error::Phase);
    }
    result
}
pub(super) fn byte(b: &Budget) -> Result<u8, Error> {
    charge(b, Charge { wire_bytes: 1, ..Charge::default() })?;
    let mut byte = [0];
    read_exact(&mut byte, b)?;
    Ok(byte[0])
}
pub(super) fn write_all(mut bytes: &[u8], b: &Budget) -> Result<(), Error> {
    let result = (|| {
        while !bytes.is_empty() {
            let count = bytes.len().min(4096);
            charge(b, Charge { work: count as u64, ..Charge::default() })?;
            // SAFETY: initialized live bytes to the protected fixed FD3 only.
            let n = unsafe { libc::write(3, bytes.as_ptr().cast(), count) };
            let error = if n < 0 { Some(std::io::Error::last_os_error()) } else { None };
            check(b)?;
            match (n, error) {
                (n, None) if n > 0 && n as usize <= count => bytes = &bytes[n as usize..],
                (_, Some(error)) if error.kind() == ErrorKind::WouldBlock => {
                    wait(libc::POLLOUT, Some(b))?
                }
                (_, Some(error)) if error.kind() == ErrorKind::Interrupted => {}
                _ => return Err(contract(b, "native fixed-channel write")),
            }
        }
        Ok(())
    })();
    if result.is_err() {
        b.refuse(trust_process_isolation::Error::Phase);
    }
    result
}
