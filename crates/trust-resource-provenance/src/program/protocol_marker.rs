//! Closed native protocol support declaration read from the original held image description.
//! This is a pre-GO protocol predicate, never custody, readiness or authority.
#[cfg(not(all(target_os = "macos", target_arch = "aarch64")))]
use std::os::unix::fs::FileExt as _;

use super::*;

#[derive(Clone, Copy)]
pub(super) enum Profile {
    Resolver,
    Workload,
    PartialCpu,
    InitialCpu,
    WorkloadMember,
    PairedQualification,
    NativeJob,
    BootstrapFixed,
    BootstrapFixedCompiler,
    BootstrapFixedLinker,
    BootstrapGraph,
}
impl Profile {
    fn section(self) -> &'static [u8; 16] {
        match self {
            Self::Resolver => b"__trust_resolve\0",
            Self::Workload => b"__trust_workload",
            Self::PartialCpu => b"__trust_partial\0",
            Self::InitialCpu => b"__trust_pinit\0\0\0",
            Self::WorkloadMember => b"__trust_member\0\0",
            Self::PairedQualification => b"__trust_pairqual",
            Self::NativeJob => b"__trust_jobroot\0",
            Self::BootstrapFixed => b"__trust_btfix\0\0\0",
            Self::BootstrapFixedCompiler => b"__trust_btfcomp\0",
            Self::BootstrapFixedLinker => b"__trust_btfld\0\0\0",
            Self::BootstrapGraph => b"__trust_bgraph\0\0",
        }
    }
    fn magic(self) -> &'static [u8; 16] {
        match self {
            Self::Resolver => b"TRUSTRESOLVER001",
            Self::Workload => b"TRUSTWORKLOAD001",
            Self::PartialCpu => b"TRUSTPARTIAL0001",
            Self::InitialCpu => b"TRUSTPARTINIT001",
            Self::WorkloadMember => b"TRUSTMEMBER00002",
            Self::PairedQualification => b"TRUSTPAIRQUAL002",
            Self::NativeJob => b"TRUSTNATIVEJOB01",
            Self::BootstrapFixed => b"TRUSTBTFIX000001",
            Self::BootstrapFixedCompiler => b"TRUSTBTFIXCOMP01",
            Self::BootstrapFixedLinker => b"TRUSTBTFIXLLD001",
            Self::BootstrapGraph => b"TRUSTBGRAPH00002",
        }
    }
    fn fields(self) -> [u64; 6] {
        match self {
            Self::Resolver => [3, 5, 32, 33, 34, 1],
            Self::Workload => [3, 6, 7, 40, 48, 1],
            Self::PartialCpu => [3, 2, 51, 53, 1, 1],
            Self::InitialCpu => [3, 5, 48, 49, 2, 3],
            Self::WorkloadMember => [3, 2, 50, 56, 57, 58],
            Self::PairedQualification => [3, 6, 7, 60, 48, 2],
            Self::NativeJob => [3, 6, 7, 106, 48, 3],
            Self::BootstrapFixed => [1, 1, 1, 1, 0, 0],
            Self::BootstrapFixedCompiler => [1, 1, 118, 2, 1, 0],
            Self::BootstrapFixedLinker => [1, 1, 1, 1, 1, 0],
            Self::BootstrapGraph => [3, 71, 72, 73, 74, 2],
        }
    }
}
const TEXT: &[u8; 16] = b"__TEXT\0\0\0\0\0\0\0\0\0\0";
fn word(bytes: &[u8], offset: usize) -> io::Result<u32> {
    Ok(u32::from_le_bytes(
        bytes
            .get(offset..offset + 4)
            .ok_or_else(|| refused("truncated protocol Mach-O word"))?
            .try_into()
            .map_err(|_| refused("protocol Mach-O word differs"))?,
    ))
}
fn wide(bytes: &[u8], offset: usize) -> io::Result<u64> {
    Ok(u64::from_le_bytes(
        bytes
            .get(offset..offset + 8)
            .ok_or_else(|| refused("truncated protocol Mach-O address"))?
            .try_into()
            .map_err(|_| refused("protocol Mach-O address differs"))?,
    ))
}
fn range(start: u64, length: u64, bound: u64) -> io::Result<std::ops::Range<u64>> {
    let end = start.checked_add(length).ok_or_else(|| refused("protocol Mach-O range overflow"))?;
    if end > bound {
        return Err(refused("protocol Mach-O range exceeds original image"));
    }
    Ok(start..end)
}
fn overlaps(a: &std::ops::Range<u64>, b: &std::ops::Range<u64>) -> bool {
    a.start < b.end && b.start < a.end
}
fn read(file: &File, output: &mut [u8], offset: u64, deadline: Instant) -> io::Result<()> {
    let mut cursor = 0;
    while cursor < output.len() {
        time(deadline)?;
        let count = file.read_at(&mut output[cursor..], offset + cursor as u64)?;
        if count == 0 {
            return Err(refused("truncated original protocol image"));
        }
        cursor += count;
    }
    Ok(())
}

/// All image/section arithmetic is checked before reading the declaration.
fn marker_offset(header: &[u8], file_length: u64, profile: Profile) -> io::Result<Option<u64>> {
    if word(header, 0)? != 0xfeed_facf || word(header, 4)? != 0x0100_000c || word(header, 12)? != 2
    {
        return Err(refused("protocol marker requires a thin arm64 Mach-O executable"));
    }
    let count = word(header, 16)? as usize;
    let bytes = word(header, 20)? as usize;
    if count == 0
        || count > MAX_COMMANDS
        || bytes > MAX_COMMAND_BYTES
        || count > bytes / 8
        || header.len() != 32 + bytes
        || header.len() as u64 > file_length
    {
        return Err(refused("protocol Mach-O commands exceed bound"));
    }
    let mut cursor = 32usize;
    let mut marker = None;
    let mut texts = 0;
    let mut segments = Vec::new();
    let mut sections = Vec::new();
    for _ in 0..count {
        let kind = word(header, cursor)?;
        let length = word(header, cursor + 4)? as usize;
        if length < 8 || length % 8 != 0 {
            return Err(refused("invalid protocol Mach-O command size"));
        }
        let next =
            cursor.checked_add(length).ok_or_else(|| refused("protocol command overflow"))?;
        let command = header
            .get(cursor..next)
            .ok_or_else(|| refused("protocol command extends beyond header"))?;
        if kind == 0x19 {
            if length < 72 {
                return Err(refused("truncated protocol segment"));
            }
            let nsects = word(command, 64)? as usize;
            if nsects > MAX_COMMANDS
                || nsects.checked_mul(80).and_then(|n| n.checked_add(72)) != Some(length)
            {
                return Err(refused("protocol segment section census differs"));
            }
            let vm = wide(command, 24)?;
            let vmsize = wide(command, 32)?;
            let fileoff = wide(command, 40)?;
            let filesize = wide(command, 48)?;
            let vmend =
                vm.checked_add(vmsize).ok_or_else(|| refused("protocol VM range overflow"))?;
            let file = range(fileoff, filesize, file_length)?;
            if !file.is_empty() {
                segments.push(file.clone());
            }
            let text = command.get(8..24) == Some(TEXT.as_slice());
            if text {
                texts += 1;
                if fileoff != 0
                    || file.end < header.len() as u64
                    || word(command, 56)? != 5
                    || word(command, 60)? != 5
                {
                    return Err(refused(
                        "protocol declaration segment is not original read-only text",
                    ));
                }
            }
            for index in 0..nsects {
                let section = &command[72 + index * 80..72 + (index + 1) * 80];
                let address = wide(section, 32)?;
                let size = wide(section, 40)?;
                let offset = word(section, 48)? as u64;
                let flags = word(section, 64)?;
                let section_type = flags & 0xff;
                let backed = !matches!(section_type, 1 | 0xc | 0x12);
                if backed && size != 0 {
                    let section_file = range(offset, size, file_length)?;
                    if section_file.start < file.start || section_file.end > file.end {
                        return Err(refused("protocol section is outside its original segment"));
                    }
                    sections.push(section_file);
                }
                if section.get(..16) == Some(profile.section().as_slice()) {
                    if marker.is_some()
                        || !text
                        || section.get(16..32) != Some(TEXT.as_slice())
                        || size != 64
                        || offset < header.len() as u64
                        || offset % 8 != 0
                        || address % 8 != 0
                        || word(section, 52)? < 3
                        || word(section, 52)? > 31
                        || flags & !0x1000_0000 != 0
                        || word(section, 56)? != 0
                        || word(section, 60)? != 0
                        || word(section, 68)? != 0
                        || word(section, 72)? != 0
                        || word(section, 76)? != 0
                        || address < vm
                        || address.checked_add(size).is_none_or(|end| end > vmend)
                        || address - vm != offset - fileoff
                    {
                        return Err(refused("protocol marker section has unsupported layout"));
                    }
                    marker = Some(offset);
                }
            }
        }
        cursor = next;
    }
    if cursor != header.len() || texts != 1 {
        return Err(refused("protocol text/command census differs"));
    }
    for ranges in [&segments, &sections] {
        for (index, left) in ranges.iter().enumerate() {
            if ranges[index + 1..].iter().any(|right| overlaps(left, right)) {
                return Err(refused("protocol image ranges overlap"));
            }
        }
    }
    Ok(marker)
}

pub(super) fn require(
    file: &File,
    profile: Profile,
    expected: &[u8; 64],
    deadline: Instant,
) -> io::Result<()> {
    let observed = declaration(file, profile, expected, deadline)?.ok_or_else(|| {
        refused("original executable does not declare native selected native protocol support")
    })?;
    if &observed != expected {
        return Err(refused("original native protocol declaration differs"));
    }
    time(deadline)
}

/// Optional support is DATA. Only a genuinely absent/different declaration is
/// false; malformed images, changed bytes and IO/deadline failures propagate.
pub(super) fn supports(
    file: &File,
    profile: Profile,
    expected: &[u8; 64],
    deadline: Instant,
) -> io::Result<bool> {
    Ok(declaration(file, profile, expected, deadline)?
        .is_some_and(|observed| observed == *expected))
}

fn declaration(
    file: &File,
    profile: Profile,
    expected: &[u8; 64],
    deadline: Instant,
) -> io::Result<Option<[u8; 64]>> {
    time(deadline)?;
    if &expected[..16] != profile.magic()
        || expected[16..]
            .as_chunks::<8>()
            .0
            .iter()
            .map(|v| u64::from_be_bytes(*v))
            .ne(profile.fields())
    {
        return Err(refused("unsupported native protocol marker format"));
    }
    let mut initial = [0u8; 32];
    read(file, &mut initial, 0, deadline)?;
    let size = word(&initial, 20)? as usize;
    if size > MAX_COMMAND_BYTES {
        return Err(refused("protocol command bytes exceed bound"));
    }
    let mut header = vec![0u8; 32 + size];
    read(file, &mut header, 0, deadline)?;
    let Some(offset) = marker_offset(&header, file.metadata()?.len(), profile)? else {
        time(deadline)?;
        return Ok(None);
    };
    let mut observed = [0u8; 64];
    read(file, &mut observed, offset, deadline)?;
    time(deadline)?;
    Ok(Some(observed))
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn initial_pair_support_is_distinct_from_legacy_and_partial_images() {
        use std::io::Write as _;
        let deadline = Instant::now() + std::time::Duration::from_secs(30);
        for profile in [Profile::Workload, Profile::PartialCpu, Profile::InitialCpu] {
            let mut file = tempfile::tempfile().unwrap();
            file.write_all(&image(profile)).unwrap();
            assert_eq!(
                supports(&file, Profile::InitialCpu, &expected(Profile::InitialCpu), deadline)
                    .unwrap(),
                matches!(profile, Profile::InitialCpu)
            );
        }
        let mut bytes = image(Profile::InitialCpu);
        bytes[256 + 63] ^= 1;
        let mut different = tempfile::tempfile().unwrap();
        different.write_all(&bytes).unwrap();
        assert!(
            !supports(&different, Profile::InitialCpu, &expected(Profile::InitialCpu), deadline)
                .unwrap()
        );
        assert!(
            require(&different, Profile::InitialCpu, &expected(Profile::InitialCpu), deadline)
                .is_err()
        );
        // A different closed declaration is unsupported; malformed image
        // layout must still be an error rather than an optional fallback.
        let mut bytes = image(Profile::InitialCpu);
        put(&mut bytes, 156, 2);
        let mut malformed = tempfile::tempfile().unwrap();
        malformed.write_all(&bytes).unwrap();
        assert!(
            supports(&malformed, Profile::InitialCpu, &expected(Profile::InitialCpu), deadline)
                .is_err()
        );
    }
    #[test]
    fn optional_partial_support_does_not_hide_malformed_or_late_original_reads() {
        use std::io::Write as _;
        let deadline = Instant::now() + std::time::Duration::from_secs(30);
        let mut legacy = tempfile::tempfile().unwrap();
        legacy.write_all(&image(Profile::Workload)).unwrap();
        assert!(
            !supports(&legacy, Profile::PartialCpu, &expected(Profile::PartialCpu), deadline)
                .unwrap()
        );
        let mut partial = tempfile::tempfile().unwrap();
        partial.write_all(&image(Profile::PartialCpu)).unwrap();
        assert!(
            supports(&partial, Profile::PartialCpu, &expected(Profile::PartialCpu), deadline)
                .unwrap()
        );
        assert!(
            supports(&partial, Profile::PartialCpu, &expected(Profile::PartialCpu), Instant::now())
                .is_err()
        );
        let mut malformed = tempfile::tempfile().unwrap();
        malformed.write_all(b"truncated original image").unwrap();
        assert!(
            supports(&malformed, Profile::PartialCpu, &expected(Profile::PartialCpu), deadline)
                .is_err()
        );
    }
    #[test]
    fn paired_linker_requires_its_own_section_and_all_effective_budget_fields() {
        use std::io::Write as _;
        let deadline = Instant::now() + std::time::Duration::from_secs(60);
        for profile in [
            Profile::BootstrapFixed,
            Profile::BootstrapFixedCompiler,
            Profile::BootstrapGraph,
            Profile::BootstrapFixedLinker,
        ] {
            let mut file = tempfile::tempfile().unwrap();
            file.write_all(&image(profile)).unwrap();
            assert_eq!(
                require(
                    &file,
                    Profile::BootstrapFixedLinker,
                    &expected(Profile::BootstrapFixedLinker),
                    deadline
                )
                .is_ok(),
                matches!(profile, Profile::BootstrapFixedLinker)
            );
        }
        for index in 0..64 {
            let mut bytes = image(Profile::BootstrapFixedLinker);
            bytes[256 + index] ^= 1;
            let mut file = tempfile::tempfile().unwrap();
            file.write_all(&bytes).unwrap();
            assert!(
                require(
                    &file,
                    Profile::BootstrapFixedLinker,
                    &expected(Profile::BootstrapFixedLinker),
                    deadline
                )
                .is_err()
            );
        }
    }

    #[test]
    fn bootstrap_fixed_declaration_is_separate_closed_and_read_from_original_bytes() {
        use std::io::Write as _;
        let deadline = Instant::now() + std::time::Duration::from_secs(30);
        for profile in [
            Profile::Resolver,
            Profile::Workload,
            Profile::WorkloadMember,
            Profile::PairedQualification,
            Profile::BootstrapFixed,
        ] {
            let mut file = tempfile::tempfile().unwrap();
            file.write_all(&image(profile)).unwrap();
            assert_eq!(
                require(
                    &file,
                    Profile::BootstrapFixed,
                    &expected(Profile::BootstrapFixed),
                    deadline
                )
                .is_ok(),
                matches!(profile, Profile::BootstrapFixed)
            );
        }
        for index in 0..64 {
            let mut bytes = image(Profile::BootstrapFixed);
            bytes[256 + index] ^= 1;
            let mut file = tempfile::tempfile().unwrap();
            file.write_all(&bytes).unwrap();
            assert!(
                require(
                    &file,
                    Profile::BootstrapFixed,
                    &expected(Profile::BootstrapFixed),
                    deadline
                )
                .is_err()
            );
        }
    }
    #[test]
    fn paired_declaration_never_reinterprets_workload_v1_or_other_held_profiles() {
        use std::io::Write as _;
        let deadline = Instant::now() + std::time::Duration::from_secs(60);
        assert_eq!(Profile::PairedQualification.section(), b"__trust_pairqual");
        assert_eq!(Profile::PairedQualification.magic(), b"TRUSTPAIRQUAL002");
        assert_eq!(Profile::PairedQualification.fields(), [3, 6, 7, 60, 48, 2]);
        for profile in [
            Profile::Resolver,
            Profile::Workload,
            Profile::WorkloadMember,
            Profile::PairedQualification,
        ] {
            let mut file = tempfile::tempfile().unwrap();
            file.write_all(&image(profile)).unwrap();
            let observed = require(
                &file,
                Profile::PairedQualification,
                &expected(Profile::PairedQualification),
                deadline,
            );
            assert_eq!(observed.is_ok(), matches!(profile, Profile::PairedQualification));
        }
        let mut paired = tempfile::tempfile().unwrap();
        paired.write_all(&image(Profile::PairedQualification)).unwrap();
        for old in [Profile::Resolver, Profile::Workload, Profile::WorkloadMember] {
            assert!(require(&paired, old, &expected(old), deadline).is_err());
        }
    }
    #[test]
    fn paired_marker_bytes_are_closed_and_cannot_borrow_workload40_fields() {
        use std::io::Write as _;
        let deadline = Instant::now() + std::time::Duration::from_secs(60);
        for index in 0..64 {
            let mut bytes = image(Profile::PairedQualification);
            bytes[256 + index] ^= 1;
            let mut file = tempfile::tempfile().unwrap();
            file.write_all(&bytes).unwrap();
            assert!(
                require(
                    &file,
                    Profile::PairedQualification,
                    &expected(Profile::PairedQualification),
                    deadline,
                )
                .is_err(),
                "mutated byte {index}"
            );
        }
    }
    #[test]
    fn paired_cost_revision_refuses_the_old_sdk_before_root_go() {
        use std::io::Write as _;
        let deadline = Instant::now() + std::time::Duration::from_secs(2);
        let mut bytes = image(Profile::PairedQualification);
        bytes[256..272].copy_from_slice(b"TRUSTPAIRQUAL001");
        let mut file = tempfile::tempfile().unwrap();
        file.write_all(&bytes).unwrap();
        assert!(
            require(
                &file,
                Profile::PairedQualification,
                &expected(Profile::PairedQualification),
                deadline
            )
            .is_err()
        );
        let mut old_expected = expected(Profile::PairedQualification);
        old_expected[..16].copy_from_slice(b"TRUSTPAIRQUAL001");
        assert!(
            require(&file, Profile::PairedQualification, &old_expected, deadline).is_err(),
            "even an old caller's expected bytes cannot relabel the closed reader profile"
        );
    }
    #[test]
    fn direct_linker_member_rejects_the_legacy_helper_only_declaration() {
        use std::io::Write as _;
        let deadline = Instant::now() + std::time::Duration::from_secs(2);
        let mut bytes = image(Profile::WorkloadMember);
        bytes[256..272].copy_from_slice(b"TRUSTMEMBER00001");
        for (index, value) in [3u64, 1, 50, 2, 3, 4].into_iter().enumerate() {
            bytes[272 + index * 8..280 + index * 8].copy_from_slice(&value.to_be_bytes());
        }
        let mut file = tempfile::tempfile().unwrap();
        file.write_all(&bytes).unwrap();
        assert!(
            require(&file, Profile::WorkloadMember, &expected(Profile::WorkloadMember), deadline)
                .is_err()
        );
    }
    #[test]
    fn compiler_member_declaration_cannot_be_an_old_root_or_resolver_protocol() {
        use std::io::Write as _;
        let deadline = Instant::now() + std::time::Duration::from_secs(2);
        for profile in [Profile::Resolver, Profile::Workload, Profile::WorkloadMember] {
            let mut file = tempfile::tempfile().unwrap();
            file.write_all(&image(profile)).unwrap();
            let observed = require(
                &file,
                Profile::WorkloadMember,
                &expected(Profile::WorkloadMember),
                deadline,
            );
            assert_eq!(observed.is_ok(), matches!(profile, Profile::WorkloadMember));
        }
        for index in 0..64 {
            let mut bytes = image(Profile::WorkloadMember);
            bytes[256 + index] ^= 1;
            let mut file = tempfile::tempfile().unwrap();
            file.write_all(&bytes).unwrap();
            assert!(
                require(
                    &file,
                    Profile::WorkloadMember,
                    &expected(Profile::WorkloadMember),
                    deadline
                )
                .is_err()
            );
        }
    }
    #[test]
    fn distinct_workload_section_and_closed_fields_never_reinterpret_a_resolver_image() {
        use std::io::Write as _;
        let deadline = Instant::now() + std::time::Duration::from_secs(2);
        let mut file = tempfile::tempfile().unwrap();
        file.write_all(&image(Profile::Workload)).unwrap();
        assert!(require(&file, Profile::Workload, &expected(Profile::Workload), deadline).is_ok());
        assert!(require(&file, Profile::Resolver, &expected(Profile::Resolver), deadline).is_err());
        let mut wrong = expected(Profile::Workload);
        wrong[31] = 5;
        assert!(require(&file, Profile::Workload, &wrong, deadline).is_err());
        let mut resolver = tempfile::tempfile().unwrap();
        resolver.write_all(&image(Profile::Resolver)).unwrap();
        assert!(
            require(&resolver, Profile::Workload, &expected(Profile::Workload), deadline).is_err()
        );
        for offset in [88, 92, 152, 156, 160, 164, 168, 176] {
            let mut altered = image(Profile::Workload);
            put(&mut altered, offset, if offset == 88 || offset == 92 { 7 } else { 1 });
            let mut file = tempfile::tempfile().unwrap();
            file.write_all(&altered).unwrap();
            assert!(
                require(&file, Profile::Workload, &expected(Profile::Workload), deadline).is_err(),
                "offset {offset}"
            );
        }
    }
    fn put(bytes: &mut [u8], offset: usize, value: u32) {
        bytes[offset..offset + 4].copy_from_slice(&value.to_le_bytes());
    }
    fn put64(bytes: &mut [u8], offset: usize, value: u64) {
        bytes[offset..offset + 8].copy_from_slice(&value.to_le_bytes());
    }
    fn expected(profile: Profile) -> [u8; 64] {
        let mut out = [0; 64];
        out[..16].copy_from_slice(profile.magic());
        for (index, value) in profile.fields().iter().enumerate() {
            out[16 + index * 8..24 + index * 8].copy_from_slice(&value.to_be_bytes());
        }
        out
    }
    fn image(profile: Profile) -> Vec<u8> {
        let mut bytes = vec![0u8; 320];
        put(&mut bytes, 0, 0xfeed_facf);
        put(&mut bytes, 4, 0x0100_000c);
        put(&mut bytes, 12, 2);
        put(&mut bytes, 16, 1);
        put(&mut bytes, 20, 152);
        put(&mut bytes, 32, 0x19);
        put(&mut bytes, 36, 152);
        bytes[40..56].copy_from_slice(TEXT);
        put64(&mut bytes, 56, 0x100000000);
        put64(&mut bytes, 64, 320);
        put64(&mut bytes, 80, 320);
        put(&mut bytes, 88, 5);
        put(&mut bytes, 92, 5);
        put(&mut bytes, 96, 1);
        bytes[104..120].copy_from_slice(profile.section());
        bytes[120..136].copy_from_slice(TEXT);
        put64(&mut bytes, 136, 0x100000100);
        put64(&mut bytes, 144, 64);
        put(&mut bytes, 152, 256);
        put(&mut bytes, 156, 3);
        bytes[256..320].copy_from_slice(&expected(profile));
        bytes
    }
    fn check(bytes: &[u8]) -> io::Result<()> {
        use std::io::Write as _;
        let mut file = tempfile::tempfile().unwrap();
        file.write_all(bytes).unwrap();
        require(
            &file,
            Profile::Resolver,
            &expected(Profile::Resolver),
            Instant::now() + std::time::Duration::from_secs(2),
        )
    }
    #[test]
    fn original_fd_marker_accepts_only_closed_native_section_and_exact_protocol() {
        assert!(check(&image(Profile::Resolver)).is_ok());
        for (offset, value) in [
            (4, 0x01000007),
            (12, 6),
            (88, 7),
            (92, 7),
            (152, 128),
            (156, 2),
            (160, 1),
            (164, 1),
            (168, 1),
            (176, 1),
        ] {
            let mut bytes = image(Profile::Resolver);
            put(&mut bytes, offset, value);
            assert!(check(&bytes).is_err(), "offset {offset}");
        }
        let mut bytes = image(Profile::Resolver);
        bytes[300] ^= 1;
        assert!(check(&bytes).is_err());
    }
    #[test]
    fn same_magic_in_arbitrary_bytes_or_mutable_data_is_no_support_declaration() {
        let mut bytes = image(Profile::Resolver);
        bytes[104] = b'X';
        assert!(check(&bytes).is_err());
        let mut bytes = image(Profile::Resolver);
        bytes[40] = b'X';
        assert!(check(&bytes).is_err());
        let mut bytes = image(Profile::Resolver);
        put64(&mut bytes, 144, 65);
        assert!(check(&bytes).is_err());
        let mut bytes = image(Profile::Resolver);
        put64(&mut bytes, 136, u64::MAX);
        assert!(check(&bytes).is_err());
    }
    #[test]
    fn original_open_description_survives_path_substitution_without_accepting_replacement() {
        use std::io::Write as _;
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("targo");
        std::fs::write(&path, image(Profile::Resolver)).unwrap();
        let original = File::open(&path).unwrap();
        std::fs::rename(&path, dir.path().join("held")).unwrap();
        File::create(&path).unwrap().write_all(b"replacement").unwrap();
        assert!(
            require(
                &original,
                Profile::Resolver,
                &expected(Profile::Resolver),
                Instant::now() + std::time::Duration::from_secs(2)
            )
            .is_ok()
        );
        assert!(
            require(
                &File::open(&path).unwrap(),
                Profile::Resolver,
                &expected(Profile::Resolver),
                Instant::now() + std::time::Duration::from_secs(2)
            )
            .is_err()
        );
        // HeldProgram's enclosing validate additionally refuses the changed path.
    }

    #[test]
    fn initial_keeper_image_requires_complete_v5_on_the_original_description() {
        let deadline = Instant::now() + std::time::Duration::from_secs(60);
        let mut current = image(Profile::InitialCpu);
        // Independent codec input: Ready v5 carries the required original
        // shadow/common-M binding. Incomplete v4 is not negotiated downward.
        current[280..288].copy_from_slice(&5u64.to_be_bytes());
        let expected: [u8; 64] = current[256..320].try_into().unwrap();
        let mut old = current.clone();
        old[280..288].copy_from_slice(&4u64.to_be_bytes());
        let old_expected: [u8; 64] = old[256..320].try_into().unwrap();
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("initial-image");
        std::fs::write(&path, &current).unwrap();
        let original = File::open(&path).unwrap();
        assert!(require(&original, Profile::InitialCpu, &expected, deadline).is_ok());
        assert!(require(&original, Profile::InitialCpu, &old_expected, deadline).is_err());
        std::fs::rename(&path, dir.path().join("held-original")).unwrap();
        std::fs::write(&path, old).unwrap();
        assert!(require(&original, Profile::InitialCpu, &expected, deadline).is_ok());
        let replacement = File::open(&path).unwrap();
        assert!(!supports(&replacement, Profile::InitialCpu, &expected, deadline).unwrap());
        assert!(require(&replacement, Profile::InitialCpu, &expected, deadline).is_err());
        assert!(require(&original, Profile::Workload, &expected, deadline).is_err());
    }

    #[test]
    fn bootstrap_graph_declaration_is_distinct_and_all_bytes_are_required() {
        use std::io::Write as _;
        let deadline = Instant::now() + std::time::Duration::from_secs(60);
        assert_eq!(Profile::BootstrapGraph.section(), b"__trust_bgraph\0\0");
        assert_eq!(Profile::BootstrapGraph.magic(), b"TRUSTBGRAPH00002");
        assert_eq!(Profile::BootstrapGraph.fields(), [3, 71, 72, 73, 74, 2]);
        let mut old = image(Profile::BootstrapGraph);
        old[256..272].copy_from_slice(b"TRUSTBGRAPH00001");
        old[312..320].copy_from_slice(&1u64.to_be_bytes());
        let mut file = tempfile::tempfile().unwrap();
        file.write_all(&old).unwrap();
        assert!(
            require(&file, Profile::BootstrapGraph, &expected(Profile::BootstrapGraph), deadline)
                .is_err()
        );
        for profile in [
            Profile::Resolver,
            Profile::Workload,
            Profile::WorkloadMember,
            Profile::PairedQualification,
            Profile::BootstrapFixed,
            Profile::BootstrapGraph,
        ] {
            let mut file = tempfile::tempfile().unwrap();
            file.write_all(&image(profile)).unwrap();
            let actual = require(
                &file,
                Profile::BootstrapGraph,
                &expected(Profile::BootstrapGraph),
                deadline,
            );
            assert_eq!(actual.is_ok(), matches!(profile, Profile::BootstrapGraph));
        }
        for index in 0..64 {
            let mut bytes = image(Profile::BootstrapGraph);
            bytes[256 + index] ^= 1;
            let mut file = tempfile::tempfile().unwrap();
            file.write_all(&bytes).unwrap();
            assert!(
                require(
                    &file,
                    Profile::BootstrapGraph,
                    &expected(Profile::BootstrapGraph),
                    deadline
                )
                .is_err()
            );
        }
    }
}
