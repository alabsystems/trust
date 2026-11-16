// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates

//! Current builtin code bound to SAME original main/driver static inputs.
//! Kernel vnode/range observations authenticate neither a writer nor machine
//! code semantics. System code remains the explicit system-runtime TCB. No
//! plugin, arbitrary process closure, SDK Ready, source or proof grant exists.

use std::sync::Arc;
use std::sync::atomic::{AtomicBool, Ordering};

use super::*;

const MAX_ANCHORS: usize = 32;
const MAX_REGIONS: usize = 65536;
const EXECUTE: u32 = 4;
const WRITE: u32 = 2;

/// Closed supported current-code input profile, not proof or SDK authority.
pub const CURRENT_CODE_POLICY: &str = "held-static-closure/current-code-macos-arm64-v1";

#[derive(Clone, Debug, PartialEq, Eq)]
struct Region {
    start: u64,
    bytes: u64,
    offset: u64,
    protection: u32,
    device: u64,
    inode: u64,
    path: Option<PathBuf>,
}
#[derive(Clone, Debug, PartialEq, Eq)]
struct Binding {
    address: u64,
    image: usize,
    region: Region,
}

/// Opaque original inputs for supplied actual builtin code anchors. Its hash
/// alone cannot reconstruct this guard or authorize replay. Retain this SAME
/// owner and revalidate before lookup/use/publication; it is not an atomic
/// process freeze, instruction-memory attestation or execution capability.
pub struct HeldExecutingProgram {
    program: Arc<HeldProgram>,
    process: process::Identity,
    anchors: Vec<Binding>,
    content: [u8; 32],
    invalid: AtomicBool,
}

// Same maintained Darwin flavor-8 layout used by aterm's SDK-checked native
// holder reader. Additional protection/offset/device fields follow the actual
// SDK sys/proc_info.h proc_regioninfo/vinfo_stat declarations. Never dladdr or a
// caller pathname/digest: this reads actual kernel VM/vnode records.
#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
fn read_region(pid: u32, address: u64) -> io::Result<Option<Region>> {
    const SIZE: usize = 1272;
    let mut bytes = [0u8; SIZE];
    let pid = i32::try_from(pid).map_err(|_| refused("current code PID overflow"))?;
    // SAFETY: a read-only native query into exactly SIZE writable bytes.
    let got =
        unsafe { libc::proc_pidinfo(pid, 8, address, bytes.as_mut_ptr().cast(), SIZE as i32) };
    if got <= 0 {
        let error = io::Error::last_os_error();
        return if error.raw_os_error() == Some(libc::EINVAL) { Ok(None) } else { Err(error) };
    }
    if got as usize != SIZE {
        return Err(refused("current executable mapping record is incomplete"));
    }
    parse_region(&bytes).map(Some)
}
#[cfg(not(all(target_os = "macos", target_arch = "aarch64")))]
fn read_region(_: u32, _: u64) -> io::Result<Option<Region>> {
    Err(io::ErrorKind::Unsupported.into())
}

#[cfg(any(test, all(target_os = "macos", target_arch = "aarch64")))]
fn parse_region(bytes: &[u8]) -> io::Result<Region> {
    if bytes.len() != 1272 {
        return Err(refused("current code mapping ABI size differs"));
    }
    let word = |at: usize| u32::from_ne_bytes(bytes[at..at + 4].try_into().unwrap());
    let long = |at: usize| u64::from_ne_bytes(bytes[at..at + 8].try_into().unwrap());
    let start = long(80);
    let size = long(88);
    if size == 0 || start.checked_add(size).is_none() {
        return Err(refused("current mapping range is empty or overflows"));
    }
    let inode = long(104);
    let path = &bytes[248..1272];
    let end = path
        .iter()
        .position(|byte| *byte == 0)
        .ok_or_else(|| refused("current mapping pathname is incomplete"))?;
    let path = if end == 0 {
        if inode != 0 {
            return Err(refused("file-backed executable mapping has no complete kernel pathname"));
        }
        None
    } else {
        if end == path.len() - 1 {
            return Err(refused("current mapping pathname may be truncated"));
        }
        use std::os::unix::ffi::OsStringExt as _;
        let path = PathBuf::from(OsString::from_vec(path[..end].to_vec()));
        canonical(&path)?;
        Some(path)
    };
    // Darwin vinfo_stat uses uint32_t; std MetadataExt normalizes dev_t,
    // which is signed on Darwin. Preserve that original device-bit meaning.
    #[cfg(target_os = "macos")]
    let device = word(96) as libc::dev_t as u64;
    #[cfg(not(target_os = "macos"))]
    let device = u64::from(word(96));
    Ok(Region { start, bytes: size, offset: long(16), protection: word(0), device, inode, path })
}
fn same_process(first: process::Identity, current: process::Identity) -> bool {
    first.pid == current.pid
        && first.birth == current.birth
        && first.unique_id == current.unique_id
        && first.exec_version == current.exec_version
}
fn images(program: &HeldProgram) -> impl Iterator<Item = &HeldFile> {
    std::iter::once(&program.executable).chain(&program.runtime)
}
fn image_index(program: &HeldProgram, region: &Region) -> Option<usize> {
    if region.inode == 0 || region.path.is_none() {
        return None;
    }
    images(program)
        .position(|file| file.before.dev() == region.device && file.before.ino() == region.inode)
}
#[cfg(any(test, all(target_os = "macos", target_arch = "aarch64")))]
fn system(region: &Region) -> bool {
    region.path.as_ref().and_then(|path| path.to_str()).is_some_and(macho::system)
}
#[cfg(not(any(test, all(target_os = "macos", target_arch = "aarch64"))))]
fn system(_: &Region) -> bool {
    false
}
fn bindings(
    program: &HeldProgram,
    current: process::Identity,
    addresses: &[u64],
    deadline: Instant,
) -> io::Result<Vec<Binding>> {
    let mut expected = vec![false; 1 + program.runtime.len()];
    let mut found = vec![None; addresses.len()];
    let mut at = 0u64;
    let mut complete = false;
    for _ in 0..MAX_REGIONS {
        time(deadline)?;
        let Some(region) = read_region(current.pid, at)? else {
            complete = true;
            break;
        };
        if region.start < at {
            return Err(refused("kernel current-code mapping walk did not advance"));
        }
        let end = region
            .start
            .checked_add(region.bytes)
            .ok_or_else(|| refused("current mapping range overflow"))?;
        if region.protection & EXECUTE != 0 {
            if region.protection & WRITE != 0 {
                return Err(refused("current code profile has a writable executable mapping"));
            }
            if let Some(index) = image_index(program, &region) {
                expected[index] = true;
                let file = images(program).nth(index).unwrap();
                for (slot, address) in addresses.iter().enumerate() {
                    if *address >= region.start && *address < end {
                        let offset = region
                            .offset
                            .checked_add(*address - region.start)
                            .ok_or_else(|| refused("current code file offset overflow"))?;
                        if offset >= file.before.len() {
                            return Err(refused(
                                "current code address lies outside original held bytes",
                            ));
                        }
                        found[slot] = Some(Binding {
                            address: *address,
                            image: index,
                            region: region.clone(),
                        });
                    }
                }
            } else if !system(&region) {
                return Err(refused(
                    "current builtin code profile has an unowned or anonymous executable mapping",
                ));
            }
        }
        at = end;
    }
    if !complete || expected.iter().any(|mapped| !mapped) || found.iter().any(Option::is_none) {
        return Err(refused(
            "actual current code does not cover SAME complete held static closure and anchors",
        ));
    }
    Ok(found.into_iter().map(Option::unwrap).collect())
}
fn content_identity(program: &HeldProgram) -> io::Result<[u8; 32]> {
    let mut files = images(program).map(|file| &file.observation).collect::<Vec<_>>();
    files.sort_by(|left, right| left.path.cmp(&right.path));
    let mut hash = <sha2::Sha256 as sha2::Digest>::new();
    let mut field = |bytes: &[u8]| {
        sha2::Digest::update(&mut hash, (bytes.len() as u64).to_le_bytes());
        sha2::Digest::update(&mut hash, bytes);
    };
    for data in [
        CURRENT_CODE_POLICY.as_bytes(),
        program.observation.policy.as_bytes(),
        program.observation.scope.as_bytes(),
    ] {
        field(data);
    }
    for file in files {
        let relative = file
            .path
            .strip_prefix(program.root())
            .map_err(|_| refused("current code original image escapes held root"))?;
        field(relative.as_os_str().as_bytes());
        field(file.sha256.as_bytes());
        field(&file.bytes.to_le_bytes());
    }
    for dependency in &program.observation.system_dependencies {
        field(dependency.as_bytes());
    }
    Ok(sha2::Digest::finalize(hash).into())
}
impl HeldProgram {
    /// Bind actual builtin bridge/kernel function pointers to original held
    /// main/driver inputs using kernel executable VM/vnode records. All required
    /// held images must actually be mapped and no unexpected non-system code
    /// may appear. This does not authorize external backends or a new SDK.
    pub fn bind_current_code(
        self: &Arc<Self>,
        anchors: &[*const ()],
        deadline: Instant,
    ) -> io::Result<HeldExecutingProgram> {
        if !cfg!(all(target_os = "macos", target_arch = "aarch64")) {
            return Err(io::ErrorKind::Unsupported.into());
        }
        if anchors.is_empty()
            || anchors.len() > MAX_ANCHORS
            || anchors.iter().any(|address| address.is_null())
        {
            return Err(refused("current code anchors are empty, unbounded or null"));
        }
        let current = process::read_identity(std::process::id())?;
        self.validate_loaded(current, deadline)?;
        let addresses = anchors.iter().map(|address| *address as usize as u64).collect::<Vec<_>>();
        let anchors = bindings(self, current, &addresses, deadline)?;
        let result = HeldExecutingProgram {
            program: self.clone(),
            process: current,
            anchors,
            content: content_identity(self)?,
            invalid: AtomicBool::new(false),
        };
        result.validate(deadline)?;
        Ok(result)
    }
}
impl HeldExecutingProgram {
    /// Stable complete held-content identity DATA, excluding ASLR, vnode IDs,
    /// absolute SDK-prefix spelling and original-owner instance. Never a grant.
    pub fn content_identity(&self) -> &[u8; 32] {
        &self.content
    }
    /// Original byte observations DATA only; not current execution or SDK proof.
    pub fn program_observation(&self) -> &ProgramObservation {
        self.program.observation()
    }
    /// Recheck the same original inputs and actual current-code mapping. Any
    /// failed/unknown/late bookend is terminal for this owner.
    pub fn validate(&self, deadline: Instant) -> io::Result<()> {
        if self.invalid.load(Ordering::Acquire) {
            return Err(refused("original current-code owner is permanently invalid"));
        }
        let result = (|| {
            time(deadline)?;
            let current = process::read_identity(std::process::id())?;
            if !same_process(self.process, current) {
                return Err(refused("current-code process/image changed"));
            }
            self.program.validate_loaded(current, deadline)?;
            let addresses = self.anchors.iter().map(|anchor| anchor.address).collect::<Vec<_>>();
            if bindings(&self.program, current, &addresses, deadline)? != self.anchors {
                return Err(refused("original executing code vnode/range changed"));
            }
            self.program.validate_loaded(current, deadline)
        })();
        if result.is_err() {
            self.invalid.store(true, Ordering::Release);
        }
        if result.is_ok() && self.invalid.load(Ordering::Acquire) {
            return Err(refused("current-code owner failed a concurrent bookend"));
        }
        result
    }
}

#[cfg(test)]
mod tests;
