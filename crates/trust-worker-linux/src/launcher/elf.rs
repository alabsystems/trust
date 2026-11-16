use std::fs::File;
use std::os::fd::AsRawFd;

use trust_process_isolation::{Budget, Charge};

use super::{checked, contract};
use crate::{Error, system};

const MAX_HEADERS: usize = 64;
const HEADER: usize = 64;
const PROGRAM: usize = 56;

fn u16_at(b: &[u8], at: usize) -> u16 {
    u16::from_le_bytes([b[at], b[at + 1]])
}
fn u32_at(b: &[u8], at: usize) -> u32 {
    u32::from_le_bytes(b[at..at + 4].try_into().unwrap_or([0; 4]))
}
fn u64_at(b: &[u8], at: usize) -> u64 {
    u64::from_le_bytes(b[at..at + 8].try_into().unwrap_or([0; 8]))
}

pub(super) fn admit(file: &File, size: u64, budget: &Budget) -> Result<(), Error> {
    let mut header = [0; HEADER];
    read_exact(file, 0, &mut header, budget)?;
    let count = inspect_header(&header, size)?;
    let offset = u64_at(&header, 32);
    let mut programs = [0; MAX_HEADERS * PROGRAM];
    let bytes = count * PROGRAM;
    read_exact(file, offset, &mut programs[..bytes], budget)?;
    budget.charge(Charge { work: 1, ..Charge::default() }).map_err(Error::Budget)?;
    // SAFETY: sysconf is a scalar native-page-size observation in the parent.
    let page = unsafe { libc::sysconf(libc::_SC_PAGESIZE) };
    if page <= 0 || !(page as u64).is_power_of_two() {
        return Err(contract("native ELF page size"));
    }
    inspect_programs(&header, &programs[..bytes], size, page as u64, budget)
}

fn read_exact(file: &File, offset: u64, bytes: &mut [u8], budget: &Budget) -> Result<(), Error> {
    let mut read = 0;
    while read < bytes.len() {
        checked(budget)?;
        budget
            .charge(Charge { work: (bytes.len() - read) as u64, ..Charge::default() })
            .map_err(Error::Budget)?;
        let off = offset
            .checked_add(read as u64)
            .and_then(|n| i64::try_from(n).ok())
            .ok_or_else(|| contract("ELF read offset"))?;
        // SAFETY: the bounded writable slice and owned FD remain live; offset
        // fits off_t and the returned count is checked before indexing.
        let n = unsafe {
            libc::pread(
                file.as_raw_fd(),
                bytes[read..].as_mut_ptr().cast(),
                bytes.len() - read,
                off,
            )
        };
        if n <= 0 || n as usize > bytes.len() - read {
            return Err(if n < 0 { system("ELF pread") } else { contract("truncated ELF") });
        }
        read += n as usize;
    }
    checked(budget)
}

fn inspect_header(b: &[u8; HEADER], size: u64) -> Result<usize, Error> {
    #[cfg(target_arch = "aarch64")]
    let machine = 183;
    #[cfg(target_arch = "x86_64")]
    let machine = 62;
    #[cfg(not(any(target_arch = "aarch64", target_arch = "x86_64")))]
    let machine = 0;
    if size < HEADER as u64
        || &b[..7] != b"\x7fELF\x02\x01\x01"
        || ![0, 3].contains(&b[7])
        || b[8..16].iter().any(|b| *b != 0)
        || u16_at(b, 16) != 2
        || machine == 0
        || u16_at(b, 18) != machine
        || u32_at(b, 20) != 1
        || u32_at(b, 48) != 0
        || u16_at(b, 52) != HEADER as u16
        || u16_at(b, 54) != PROGRAM as u16
    {
        return Err(contract("static native ELF header"));
    }
    let count = usize::from(u16_at(b, 56));
    if count == 0 || count > MAX_HEADERS {
        return Err(contract("ELF header count"));
    }
    let end = u64_at(b, 32)
        .checked_add((count * PROGRAM) as u64)
        .ok_or_else(|| contract("ELF program range"))?;
    if u64_at(b, 32) < HEADER as u64 || end > size {
        return Err(contract("ELF program range"));
    }
    Ok(count)
}

fn inspect_programs(
    header: &[u8; HEADER],
    programs: &[u8],
    size: u64,
    page: u64,
    budget: &Budget,
) -> Result<(), Error> {
    let mut loads = [(0u64, 0u64); MAX_HEADERS];
    let mut used = 0;
    let mut entry = false;
    let mut stack = false;
    for p in programs.chunks_exact(PROGRAM) {
        checked(budget)?;
        budget
            .charge(Charge { work: PROGRAM as u64 + used as u64, ..Charge::default() })
            .map_err(Error::Budget)?;
        let kind = u32_at(p, 0);
        let flags = u32_at(p, 4);
        if [2, 3, 5].contains(&kind) {
            return Err(contract("dynamic ELF route"));
        }
        if kind == 0x6474e551 {
            if stack || flags & !7 != 0 || flags & 1 != 0 {
                return Err(contract("ELF stack"));
            }
            stack = true;
        }
        if kind != 1 {
            continue;
        }
        let offset = u64_at(p, 8);
        let address = u64_at(p, 16);
        let file_size = u64_at(p, 32);
        let memory_size = u64_at(p, 40);
        let alignment = u64_at(p, 48);
        let file_end =
            offset.checked_add(file_size).ok_or_else(|| contract("ELF file overflow"))?;
        let end =
            address.checked_add(memory_size).ok_or_else(|| contract("ELF memory overflow"))?;
        if file_size > memory_size
            || file_end > size
            || flags & !7 != 0
            || flags & 3 == 3
            || memory_size == 0
            || offset % page != address % page
            || (alignment > 1
                && (!alignment.is_power_of_two() || offset % alignment != address % alignment))
        {
            return Err(contract("ELF LOAD shape"));
        }
        let page_start = address & !(page - 1);
        let page_end = end.checked_add(page - 1).ok_or_else(|| contract("ELF rounded overflow"))?
            & !(page - 1);
        // Even disjoint byte intervals can occupy the same kernel mapping page
        // and overwrite its permissions/content. This narrow route rejects all
        // rounded LOAD overlap, rather than infer safe permission composition.
        if loads[..used].iter().any(|(a, z)| page_start < *z && *a < page_end) {
            return Err(contract("ELF LOAD page overlap"));
        }
        loads[used] = (page_start, page_end);
        used += 1;
        entry |= flags & 1 != 0
            && u64_at(header, 24) >= address
            && u64_at(header, 24)
                < address.checked_add(file_size).ok_or_else(|| contract("ELF entry overflow"))?;
    }
    if !stack || !entry || used == 0 {
        return Err(contract("ELF entry/stack"));
    }
    checked(budget)
}

#[cfg(test)]
mod tests {
    use std::time::{Duration, Instant};

    use trust_process_isolation::Limits;

    use super::*;
    fn budget(work: u64) -> Budget {
        Budget::new(
            Limits {
                frame_bytes: 1024,
                wire_bytes: 4096,
                allocation_bytes: 4096,
                values: 100,
                work,
                calls: 10,
                live_handles: 2,
                depth: 8,
            },
            Instant::now() + Duration::from_secs(5),
        )
        .unwrap()
    }
    fn image() -> ([u8; HEADER], [u8; PROGRAM * 2]) {
        let mut h = [0; HEADER];
        h[..7].copy_from_slice(b"\x7fELF\x02\x01\x01");
        h[16..18].copy_from_slice(&2u16.to_le_bytes());
        h[18..20].copy_from_slice(
            &(if cfg!(target_arch = "aarch64") { 183u16 } else { 62 }).to_le_bytes(),
        );
        h[20..24].copy_from_slice(&1u32.to_le_bytes());
        h[24..32].copy_from_slice(&0x400000u64.to_le_bytes());
        h[32..40].copy_from_slice(&64u64.to_le_bytes());
        h[52..54].copy_from_slice(&64u16.to_le_bytes());
        h[54..56].copy_from_slice(&56u16.to_le_bytes());
        h[56..58].copy_from_slice(&2u16.to_le_bytes());
        let mut p = [0; PROGRAM * 2];
        p[..4].copy_from_slice(&1u32.to_le_bytes());
        p[4..8].copy_from_slice(&5u32.to_le_bytes());
        p[16..24].copy_from_slice(&0x400000u64.to_le_bytes());
        p[32..40].copy_from_slice(&4096u64.to_le_bytes());
        p[40..48].copy_from_slice(&4096u64.to_le_bytes());
        p[48..56].copy_from_slice(&4096u64.to_le_bytes());
        p[56..60].copy_from_slice(&0x6474e551u32.to_le_bytes());
        p[60..64].copy_from_slice(&6u32.to_le_bytes());
        (h, p)
    }
    #[test]
    fn native_static_exact_work_and_one_short() {
        let (h, p) = image();
        assert_eq!(inspect_header(&h, 4096).unwrap(), 2);
        assert!(inspect_programs(&h, &p, 4096, 4096, &budget(113)).is_ok());
        let b = budget(112);
        assert!(inspect_programs(&h, &p, 4096, 4096, &b).is_err());
        assert!(b.clone().check().is_err());
    }
    #[test]
    fn refuses_header_and_program_domain_mutations() {
        let (h, p) = image();
        for (at, value) in [
            (4, 1),
            (5, 2),
            (7, 255),
            (8, 1),
            (48, 1),
            (16, 3),
            (18, 0),
            (52, 0),
            (54, 0),
            (56, 65),
        ] {
            let mut q = h;
            q[at] = value;
            assert!(inspect_header(&q, 4096).is_err(), "{at}");
        }
        for (at, value) in [(0, 2), (0, 3), (4, 7), (60, 7)] {
            let mut q = p;
            q[at] = value;
            assert!(inspect_programs(&h, &q, 4096, 4096, &budget(10000)).is_err(), "{at}");
        }
        let mut q = p;
        q[40..48].copy_from_slice(&u64::MAX.to_le_bytes());
        assert!(inspect_programs(&h, &q, 4096, 4096, &budget(10000)).is_err());
        let mut q = h;
        q[32..40].copy_from_slice(&u64::MAX.to_le_bytes());
        assert!(inspect_header(&q, 4096).is_err());
    }
    #[test]
    fn native_pages_reject_hidden_overlap_and_incongruence() {
        let (h, p) = image();
        let mut programs = [0; PROGRAM * 3];
        programs[..PROGRAM * 2].copy_from_slice(&p);
        programs[32..40].copy_from_slice(&2048u64.to_le_bytes());
        programs[40..48].copy_from_slice(&2048u64.to_le_bytes());
        let q = &mut programs[PROGRAM * 2..];
        q[..4].copy_from_slice(&1u32.to_le_bytes());
        q[4..8].copy_from_slice(&6u32.to_le_bytes());
        q[8..16].copy_from_slice(&2048u64.to_le_bytes());
        q[16..24].copy_from_slice(&0x400800u64.to_le_bytes());
        q[32..40].copy_from_slice(&2048u64.to_le_bytes());
        q[40..48].copy_from_slice(&2048u64.to_le_bytes());
        assert!(inspect_programs(&h, &programs, 4096, 4096, &budget(10000)).is_err());
        let mut q = p;
        q[8..16].copy_from_slice(&1u64.to_le_bytes());
        q[32..40].copy_from_slice(&4095u64.to_le_bytes());
        q[48..56].copy_from_slice(&1u64.to_le_bytes());
        assert!(inspect_programs(&h, &q, 4096, 4096, &budget(10000)).is_err());
    }
}
