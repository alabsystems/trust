//! Bounded historical kernel map observations, not execution or an atomic mm
//! snapshot. Only the separately supervised broker may perform these preads.
use std::fs::File;
use std::os::fd::{AsRawFd, RawFd};

use trust_process_isolation::{Budget, Charge};

use super::kernel::{FileIdentity, IssuedDescriptor};
use super::{charge, check, contract, reserve};
use crate::{Error, system};

const BYTES: usize = 256 * 1024;
const RECORDS: usize = 1024;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) struct ExecutableMapping {
    pub start: u64,
    pub end: u64,
    pub offset: u64,
    pub file: FileIdentity,
}
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) struct ObservedMapping {
    pub object: u8,
    pub mapping: ExecutableMapping,
}
pub(super) struct Mappings {
    maps: File,
    budget: Budget,
    page: u64,
    bytes: Vec<u8>,
    baseline: Vec<ExecutableMapping>,
    observed: Vec<ObservedMapping>,
}
impl Mappings {
    /// Trusted entry is still at its pre-load rendezvous. The caller already
    /// authenticated this retained exact post-exec procfs handle and owns the
    /// original child/pidfd. No pathname, task marker or worker map text is used.
    pub fn prepare(maps: File, budget: &Budget) -> Result<Self, Error> {
        check(budget)?;
        // SAFETY: scalar page-size query before broker confinement.
        let page = unsafe { libc::sysconf(libc::_SC_PAGESIZE) };
        let page = u64::try_from(page).map_err(|_| contract(budget, "native map page size"))?;
        if !page.is_power_of_two() || page > 65536 {
            return Err(contract(budget, "native map page granule"));
        }
        let mut bytes = reserve(BYTES + 1, budget)?;
        charge(budget, Charge { work: (BYTES + 1) as u64, ..Charge::default() })?;
        bytes.resize(BYTES + 1, 0);
        let baseline = reserve(RECORDS, budget)?;
        let observed = reserve(RECORDS, budget)?;
        let mut result = Self { maps, budget: budget.clone(), page, bytes, baseline, observed };
        let used = result.read()?;
        scan(&result.bytes[..used], &result.budget, |mapping| {
            if result.baseline.len() == RECORDS {
                return Err(contract(&result.budget, "native baseline mapping count"));
            }
            result.baseline.push(mapping);
            Ok(())
        })?;
        check(budget)?;
        Ok(result)
    }
    pub fn fd(&self) -> RawFd {
        self.maps.as_raw_fd()
    }
    pub fn file(&self) -> &File {
        &self.maps
    }
    pub fn page(&self) -> u64 {
        self.page
    }
    pub fn observe(&mut self, issued: &[IssuedDescriptor]) -> Result<&[ObservedMapping], Error> {
        let result = self.observe_inner(issued);
        if result.is_err() {
            self.budget.refuse(trust_process_isolation::Error::Phase);
        }
        result?;
        Ok(&self.observed)
    }
    fn observe_inner(&mut self, issued: &[IssuedDescriptor]) -> Result<(), Error> {
        if issued.len() > 31 {
            return Err(contract(&self.budget, "native issued mapping inventory bound"));
        }
        self.observed.clear();
        let used = self.read()?;
        scan(&self.bytes[..used], &self.budget, |mapping| {
            charge(
                &self.budget,
                Charge {
                    work: 64 * (self.baseline.len() + issued.len() + 1) as u64,
                    ..Charge::default()
                },
            )?;
            if self.baseline.contains(&mapping) {
                return Ok(());
            }
            let source = issued
                .iter()
                .find(|source| source.file == mapping.file)
                .ok_or_else(|| contract(&self.budget, "unissued executable native map"))?;
            let size = source
                .size
                .checked_add(self.page - 1)
                .map(|n| n & !(self.page - 1))
                .ok_or_else(|| contract(&self.budget, "native map file span"))?;
            if mapping.offset % self.page != 0
                || mapping.start % self.page != 0
                || mapping.end % self.page != 0
                || mapping
                    .offset
                    .checked_add(mapping.end - mapping.start)
                    .is_none_or(|end| end > size)
                || self.observed.len() == RECORDS
            {
                return Err(contract(&self.budget, "native executable map bounds"));
            }
            self.observed.push(ObservedMapping { object: source.object, mapping });
            Ok(())
        })?;
        check(&self.budget)
    }
    fn read(&mut self) -> Result<usize, Error> {
        charge(&self.budget, Charge { work: 8 * BYTES as u64, ..Charge::default() })?;
        let mut used = 0;
        loop {
            charge(&self.budget, Charge { work: 64, ..Charge::default() })?;
            if used == self.bytes.len() {
                return Err(contract(&self.budget, "native map byte bound"));
            }
            // SAFETY: the sole broker reader owns the retained maps descriptor,
            // output is bounded, and offset stays within the fixed byte bound.
            let n = unsafe {
                libc::pread(
                    self.maps.as_raw_fd(),
                    self.bytes[used..].as_mut_ptr().cast(),
                    self.bytes.len() - used,
                    used as i64,
                )
            };
            if n < 0 {
                return Err(system("native retained maps read"));
            }
            if n == 0 {
                check(&self.budget)?;
                return Ok(used);
            }
            let n = n as usize;
            if n > self.bytes.len() - used || used + n > BYTES {
                return Err(contract(&self.budget, "native map byte count"));
            }
            used += n;
        }
    }
}

fn scan(
    bytes: &[u8],
    b: &Budget,
    mut visit: impl FnMut(ExecutableMapping) -> Result<(), Error>,
) -> Result<(), Error> {
    let text = std::str::from_utf8(bytes).map_err(|_| contract(b, "native maps encoding"))?;
    if !text.ends_with('\n') {
        return Err(contract(b, "native maps truncated record"));
    }
    let mut count = 0;
    for line in text.lines() {
        charge(b, Charge { work: 64, ..Charge::default() })?;
        count += 1;
        if count > RECORDS {
            return Err(contract(b, "native map record count"));
        }
        let mut fields = line.split_whitespace();
        let span = fields.next().ok_or_else(|| contract(b, "native map address"))?;
        let permissions =
            fields.next().ok_or_else(|| contract(b, "native map permissions"))?.as_bytes();
        let offset = fields.next().ok_or_else(|| contract(b, "native map offset"))?;
        let device = fields.next().ok_or_else(|| contract(b, "native map device"))?;
        let inode = fields.next().ok_or_else(|| contract(b, "native map inode"))?;
        if permissions.len() != 4
            || ![b'r', b'-'].contains(&permissions[0])
            || ![b'w', b'-'].contains(&permissions[1])
            || ![b'x', b'-'].contains(&permissions[2])
            || ![b'p', b's'].contains(&permissions[3])
            || permissions[1] == b'w' && permissions[2] == b'x'
        {
            return Err(contract(b, "native map protection"));
        }
        let (start, end) =
            span.split_once('-').ok_or_else(|| contract(b, "native map address pair"))?;
        let start = number(start, 16, b)?;
        let end = number(end, 16, b)?;
        if start >= end {
            return Err(contract(b, "native map address extent"));
        }
        let (major, minor) =
            device.split_once(':').ok_or_else(|| contract(b, "native map device pair"))?;
        let major =
            u32::try_from(number(major, 16, b)?).map_err(|_| contract(b, "native map major"))?;
        let minor =
            u32::try_from(number(minor, 16, b)?).map_err(|_| contract(b, "native map minor"))?;
        let mapping = ExecutableMapping {
            start,
            end,
            offset: number(offset, 16, b)?,
            file: FileIdentity {
                device: libc::makedev(major, minor),
                inode: number(inode, 10, b)?,
            },
        };
        if permissions[2] == b'x' {
            visit(mapping)?;
        }
    }
    check(b)
}
fn number(value: &str, radix: u32, b: &Budget) -> Result<u64, Error> {
    if value.is_empty()
        || value.len() > if radix == 16 { 16 } else { 20 }
        || !value
            .bytes()
            .all(|c| if radix == 16 { c.is_ascii_hexdigit() } else { c.is_ascii_digit() })
    {
        return Err(contract(b, "native map integer grammar"));
    }
    u64::from_str_radix(value, radix).map_err(|_| contract(b, "native map integer overflow"))
}
