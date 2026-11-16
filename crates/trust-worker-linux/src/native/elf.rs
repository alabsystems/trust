//! Bounded structural ET_DYN admission, not a proof that a native loader can
//! interpret every relocation/symbol or that a DSO is memory safe.
use std::fs::File;
use std::os::fd::AsRawFd;

use trust_process_isolation::{Budget, Charge};

use super::closure::NativeObjectPlan;
use super::{NAME, charge, check, contract};
use crate::launcher::snapshot::Snapshot;
use crate::{Error, system};

const HEADERS: usize = 64;
const PROGRAM: usize = 56;
const DYNAMIC: usize = 256;

fn u16at(b: &[u8], n: usize) -> u16 {
    u16::from_le_bytes([b[n], b[n + 1]])
}
fn u32at(b: &[u8], n: usize) -> u32 {
    u32::from_le_bytes([b[n], b[n + 1], b[n + 2], b[n + 3]])
}
fn u64at(b: &[u8], n: usize) -> u64 {
    u64::from_le_bytes([b[n], b[n + 1], b[n + 2], b[n + 3], b[n + 4], b[n + 5], b[n + 6], b[n + 7]])
}

pub(super) fn admit(s: &Snapshot, plan: &NativeObjectPlan<'_>, b: &Budget) -> Result<(), Error> {
    let mut h = [0; 64];
    read(&s.file, 0, &mut h, b)?;
    #[cfg(target_arch = "aarch64")]
    let machine = 183;
    #[cfg(target_arch = "x86_64")]
    let machine = 62;
    #[cfg(not(any(target_arch = "aarch64", target_arch = "x86_64")))]
    let machine = 0;
    charge(b, Charge { work: 64, ..Charge::default() })?;
    if &h[..7] != b"\x7fELF\x02\x01\x01"
        || ![0, 3].contains(&h[7])
        || h[8..16].iter().any(|n| *n != 0)
        || u16at(&h, 16) != 3
        || machine == 0
        || u16at(&h, 18) != machine
        || u32at(&h, 20) != 1
        || u32at(&h, 48) != 0
        || u16at(&h, 52) != 64
        || u16at(&h, 54) != PROGRAM as u16
    {
        return Err(contract(b, "native DSO ELF header"));
    }
    let count = usize::from(u16at(&h, 56));
    let offset = u64at(&h, 32);
    if count == 0
        || count > HEADERS
        || offset < 64
        || offset.checked_add((count * PROGRAM) as u64).is_none_or(|end| end > s.size)
    {
        return Err(contract(b, "native DSO program table"));
    }
    let mut programs = [0; HEADERS * PROGRAM];
    read(&s.file, offset, &mut programs[..count * PROGRAM], b)?;
    // SAFETY: sysconf observes the native page size; no pointer is involved.
    let page = unsafe { libc::sysconf(libc::_SC_PAGESIZE) };
    if page <= 0 || !(page as u64).is_power_of_two() {
        return Err(contract(b, "native DSO page"));
    }
    let page = page as u64;
    let mut loads = [(0u64, 0u64, 0u64, 0u64, 0u64); HEADERS];
    let mut used = 0;
    let mut dynrange = None;
    let mut stack = false;
    let mut executable = false;
    for p in programs[..count * PROGRAM].chunks_exact(PROGRAM) {
        charge(b, Charge { work: PROGRAM as u64 + used as u64, ..Charge::default() })?;
        let kind = u32at(p, 0);
        let flags = u32at(p, 4);
        if !matches!(kind, 0 | 1 | 2 | 4 | 6 | 7 | 0x6474e550..=0x6474e553) {
            return Err(contract(b, "unknown native program tag"));
        }
        let off = u64at(p, 8);
        let addr = u64at(p, 16);
        let files = u64at(p, 32);
        let mem = u64at(p, 40);
        let align = u64at(p, 48);
        if [3, 5].contains(&kind) {
            return Err(contract(b, "native DSO interpreter"));
        }
        if kind == 0x6474e551 {
            if stack || flags & !7 != 0 || flags & 1 != 0 {
                return Err(contract(b, "native DSO stack"));
            }
            stack = true;
        }
        if kind == 2 {
            if dynrange.is_some()
                || files == 0
                || files % 16 != 0
                || files > (DYNAMIC * 16) as u64
                || off.checked_add(files).is_none_or(|end| end > s.size)
            {
                return Err(contract(b, "native DSO dynamic bounds"));
            }
            dynrange = Some((off, addr, files));
        }
        if kind != 1 {
            continue;
        }
        let end = addr.checked_add(mem).ok_or_else(|| contract(b, "native DSO LOAD overflow"))?;
        let rounded =
            end.checked_add(page - 1).ok_or_else(|| contract(b, "native DSO page overflow"))?
                & !(page - 1);
        let start = addr & !(page - 1);
        if mem == 0
            || files > mem
            || off.checked_add(files).is_none_or(|end| end > s.size)
            || flags & !7 != 0
            || flags & 3 == 3
            || off % page != addr % page
            || (align > 1 && (!align.is_power_of_two() || off % align != addr % align))
            || loads[..used].iter().any(|(a, z, _, _, _)| start < *z && *a < rounded)
        {
            return Err(contract(b, "native DSO LOAD shape"));
        }
        loads[used] = (start, rounded, addr, off, files);
        used += 1;
        executable |= flags & 1 != 0 && files != 0;
    }
    if !stack || !executable {
        return Err(contract(b, "native DSO executable/stack"));
    }
    let (off, addr, files) = dynrange.ok_or_else(|| contract(b, "native DSO missing dynamic"))?;
    if translate(addr, files, &loads[..used], b)? != off {
        return Err(contract(b, "native DSO dynamic mapping"));
    }
    let mut table = [0; DYNAMIC * 16];
    read(&s.file, off, &mut table[..files as usize], b)?;
    dynamic(&s.file, &table[..files as usize], &loads[..used], plan, b)
}

fn dynamic(
    f: &File,
    table: &[u8],
    loads: &[(u64, u64, u64, u64, u64)],
    plan: &NativeObjectPlan<'_>,
    b: &Budget,
) -> Result<(), Error> {
    let mut tags = [0u64; DYNAMIC];
    let mut used = 0;
    let mut straddr = None;
    let mut strsize = None;
    let mut soname = None;
    let mut needs = [0u64; super::OBJECTS];
    let mut count = 0;
    let mut ended = false;
    for entry in table.chunks_exact(16) {
        charge(b, Charge { work: 16 + used as u64, ..Charge::default() })?;
        let tag = u64at(entry, 0);
        let value = u64at(entry, 8);
        if ended {
            if tag != 0 || value != 0 {
                return Err(contract(b, "native dynamic tail"));
            }
            continue;
        }
        if tag == 0 {
            ended = true;
            if value != 0 {
                return Err(contract(b, "native DT_NULL"));
            }
            continue;
        }
        if tag != 1 && tags[..used].contains(&tag) {
            return Err(contract(b, "duplicate native dynamic tag"));
        }
        tags[used] = tag;
        used += 1;
        match tag {
            1 => {
                if count == needs.len() {
                    return Err(contract(b, "native needed count"));
                }
                needs[count] = value;
                count += 1;
            }
            5 => straddr = Some(value),
            10 => strsize = Some(value),
            14 => soname = Some(value),
            // Recognized structural metadata only; the confined loader must
            // still qualify actual relocation/TLS/symbol behavior separately.
            2..=4
            | 6..=9
            | 11..=13
            | 17..=20
            | 23..=29
            | 32..=37
            | 0x6ffffef5
            | 0x6ffffff0
            | 0x6ffffff9
            | 0x6ffffffa
            | 0x6ffffffc..=0x6fffffff => {
                if [15, 22, 29, 32].contains(&tag) {
                    return Err(contract(b, "native dynamic path/text authority"));
                }
            }
            30 if value & !(8 | 16) == 0 => (),
            0x6ffffffb if value & !(1 | 8 | 0x800) == 0 => (),
            _ => return Err(contract(b, "unknown native dynamic tag/flags")),
        }
    }
    let size = strsize.ok_or_else(|| contract(b, "native missing STRSZ"))?;
    if !ended || size == 0 || size > 1024 * 1024 || count != plan.needed.len() {
        return Err(contract(b, "native dynamic strings"));
    }
    let base =
        translate(straddr.ok_or_else(|| contract(b, "native missing STRTAB"))?, size, loads, b)?;
    string(
        f,
        base,
        size,
        soname.ok_or_else(|| contract(b, "native missing SONAME"))?,
        plan.soname.as_bytes(),
        b,
    )?;
    for (n, expected) in needs[..count].iter().zip(plan.needed) {
        string(f, base, size, *n, expected.as_bytes(), b)?;
    }
    check(b)
}
fn translate(
    addr: u64,
    size: u64,
    loads: &[(u64, u64, u64, u64, u64)],
    b: &Budget,
) -> Result<u64, Error> {
    charge(b, Charge { work: loads.len() as u64, ..Charge::default() })?;
    let end = addr.checked_add(size).ok_or_else(|| contract(b, "native virtual range"))?;
    let found = loads.iter().find(|(_, _, base, _, len)| {
        addr >= *base && base.checked_add(*len).is_some_and(|z| end <= z)
    });
    let (_, _, base, off, _) = found.ok_or_else(|| contract(b, "native unmapped file range"))?;
    off.checked_add(addr - base).ok_or_else(|| contract(b, "native file range"))
}
fn string(
    f: &File,
    base: u64,
    size: u64,
    at: u64,
    expected: &[u8],
    b: &Budget,
) -> Result<(), Error> {
    let n = expected.len().checked_add(1).ok_or_else(|| contract(b, "native string overflow"))?;
    if n > NAME + 1 || at.checked_add(n as u64).is_none_or(|end| end > size) {
        return Err(contract(b, "native string bounds"));
    }
    let mut bytes = [0; NAME + 1];
    read(
        f,
        base.checked_add(at).ok_or_else(|| contract(b, "native string offset"))?,
        &mut bytes[..n],
        b,
    )?;
    charge(b, Charge { work: n as u64, ..Charge::default() })?;
    if bytes[n - 1] != 0 || &bytes[..n - 1] != expected {
        return Err(contract(b, "native string identity"));
    }
    Ok(())
}
fn read(f: &File, off: u64, bytes: &mut [u8], b: &Budget) -> Result<(), Error> {
    let mut n = 0;
    while n < bytes.len() {
        charge(b, Charge { work: (bytes.len() - n) as u64, ..Charge::default() })?;
        let offset = off
            .checked_add(n as u64)
            .and_then(|o| i64::try_from(o).ok())
            .ok_or_else(|| contract(b, "native pread offset"))?;
        // SAFETY: the slice is writable for the requested bounded length and
        // the owned immutable FD stays live; offset fits off_t, result checked.
        let got = unsafe {
            libc::pread(f.as_raw_fd(), bytes[n..].as_mut_ptr().cast(), bytes.len() - n, offset)
        };
        if got <= 0 || got as usize > bytes.len() - n {
            return Err(if got < 0 {
                system("native ELF pread")
            } else {
                contract(b, "native ELF truncation")
            });
        }
        n += got as usize;
    }
    check(b)
}
