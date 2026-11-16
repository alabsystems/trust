//! Trust: platform inputs of a confined compiler action.
//!
//! A capture has two parts (PORTABLE-PLATFORM-IDENTITY-1):
//!
//! * the **image identity**, which [`PlatformInputs::digest`] returns and the
//!   unit fingerprint keys: the CPU and OS-image facts an action's output may
//!   depend on, the loaded dyld shared cache and the bytes of the system
//!   version file;
//! * the **local binding**, which [`PlatformInputs::binding`] returns: this
//!   boot, its CPU and memory counts, its file limit and the mounts that serve
//!   the platform roots. The binding is never keyed. [`PlatformInputs::ensure_current`]
//!   compares it, with the image, at every execution edge.
//!
//! Mount identities are not keyed, so the image must fix system file content:
//! every platform root must be on the read-only root snapshot of a volume that
//! reports itself cryptographically sealed, or the capture refuses.
//!
//! Two Macs on one image may compute one digest. Nothing here fetches,
//! publishes or authorizes a record from another Mac.

use anyhow::{Result, bail};

pub const PLATFORM_READ_DIRECTORIES: &[&str] = &[
    "/System/Library/Frameworks/CoreFoundation.framework",
    "/System/Library/Frameworks/Security.framework",
    "/usr/lib",
];
pub const PLATFORM_READ_FILES: &[&str] = &["/System/Library/CoreServices/SystemVersion.plist"];
/// Every sysctl a confined action may read. Each is captured in exactly one
/// part: [`IMAGE_SYSCTLS`] or [`BINDING_SYSCTLS`]; capture refuses otherwise.
pub(crate) const PLATFORM_SYSCTLS: &[&str] = &[
    "hw.activecpu",
    "hw.cachelinesize",
    "hw.cpufamily",
    "hw.cpusubtype",
    "hw.cputype",
    "hw.logicalcpu",
    "hw.logicalcpu_max",
    "hw.machine",
    "hw.memsize",
    "hw.ncpu",
    "hw.pagesize",
    "hw.pagesize_compat",
    "hw.physicalcpu",
    "hw.physicalcpu_max",
    "kern.bootsessionuuid",
    "kern.iossupportversion",
    "kern.maxfilesperproc",
    "kern.osproductversion",
    "kern.osrelease",
    "kern.ostype",
    "kern.osversion",
    "kern.version",
    "sysctl.proc_translated",
];
/// The OS image and CPU: the instruction set and its generation, page and
/// cache-line geometry, Rosetta translation, and the exact OS build and
/// kernel. Keyed.
#[cfg_attr(not(target_os = "macos"), allow(dead_code))]
const IMAGE_SYSCTLS: &[&str] = &[
    "hw.cachelinesize",
    "hw.cpufamily",
    "hw.cpusubtype",
    "hw.cputype",
    "hw.machine",
    "hw.pagesize",
    "hw.pagesize_compat",
    "kern.iossupportversion",
    "kern.osproductversion",
    "kern.osrelease",
    "kern.ostype",
    "kern.osversion",
    "kern.version",
    "sysctl.proc_translated",
];
/// One boot of one Mac: its session, how many CPUs and how much memory it
/// has, and its file limit. A compiler may size its work by these; none
/// selects the bytes it writes. Compared, never keyed.
#[cfg_attr(not(target_os = "macos"), allow(dead_code))]
const BINDING_SYSCTLS: &[&str] = &[
    "hw.activecpu",
    "hw.logicalcpu",
    "hw.logicalcpu_max",
    "hw.memsize",
    "hw.ncpu",
    "hw.physicalcpu",
    "hw.physicalcpu_max",
    "kern.bootsessionuuid",
    "kern.maxfilesperproc",
];
/// The largest system version file a capture reads.
#[cfg_attr(not(target_os = "macos"), allow(dead_code))]
const PLATFORM_FILE_LIMIT: u64 = 64 * 1024;

#[derive(Clone, Debug)]
pub struct PlatformInputs {
    image: String,
    binding: String,
}

impl PlatformInputs {
    pub fn capture() -> Result<Self> {
        #[cfg(target_os = "macos")]
        {
            capture_from(&LocalMac)
        }
        #[cfg(not(target_os = "macos"))]
        {
            bail!("confined platform inputs are not implemented on this platform")
        }
    }

    /// The OS image identity: the platform part of a confined unit's key.
    pub fn digest(&self) -> &str {
        &self.image
    }

    /// This boot's binding of the image. Never part of a key: two boots, or
    /// two Macs, on one image share a digest and differ here.
    pub fn binding(&self) -> &str {
        &self.binding
    }

    /// Refuse unless both the image and its local binding are unchanged.
    pub fn ensure_current(&self) -> Result<()> {
        #[cfg(target_os = "macos")]
        {
            self.ensure_current_from(&LocalMac)
        }
        #[cfg(not(target_os = "macos"))]
        {
            bail!("confined platform inputs are not implemented on this platform")
        }
    }

    #[cfg(target_os = "macos")]
    fn ensure_current_from(&self, facts: &dyn PlatformFacts) -> Result<()> {
        let current = capture_from(facts)?;
        if current.image != self.image {
            bail!("confined action platform image changed");
        }
        if current.binding != self.binding {
            bail!("confined action local platform binding changed");
        }
        Ok(())
    }
}

/// Where a capture reads its facts. The production source is [`LocalMac`];
/// tests inject facts to vary each one through the same capture code.
#[cfg(target_os = "macos")]
trait PlatformFacts {
    fn architecture(&self) -> &str;
    fn sysctl(&self, name: &str) -> Result<Option<Vec<u8>>>;
    fn shared_cache_uuid(&self) -> Result<[u8; 16]>;
    /// At most `limit + 1` bytes of a platform file.
    fn file(&self, path: &std::path::Path, limit: u64) -> Result<Vec<u8>>;
    fn volume(&self, path: &std::path::Path) -> Result<PlatformVolume>;
}

/// What the file system reports about the volume serving one platform path.
#[cfg(target_os = "macos")]
#[derive(Clone, Debug)]
struct PlatformVolume {
    /// The path with every link resolved.
    canonical: Vec<u8>,
    /// `statfs` mount flags.
    mount_flags: u32,
    /// `VOL_CAPABILITIES_FORMAT` words of `ATTR_VOL_CAPABILITIES`.
    format_capabilities: u32,
    format_valid: u32,
    device: u64,
    filesystem: Vec<u8>,
    mounted_from: Vec<u8>,
}

#[cfg(target_os = "macos")]
fn capture_from(facts: &dyn PlatformFacts) -> Result<PlatformInputs> {
    use crate::Sha256;
    fn field(hash: &mut Sha256, bytes: &[u8]) {
        hash.update(&(bytes.len() as u64).to_le_bytes());
        hash.update(bytes);
    }
    let mut image = Sha256::new();
    let mut binding = Sha256::new();
    field(&mut image, b"targo-platform-image-identity-v2");
    field(&mut binding, b"targo-platform-local-binding-v2");

    // Refuse before hashing anything a volume cannot vouch for.
    let mut mounts = Vec::new();
    for path in PLATFORM_READ_DIRECTORIES.iter().chain(PLATFORM_READ_FILES) {
        mounts.push((
            path,
            sealed_snapshot_mount(facts, std::path::Path::new(path))?,
        ));
    }

    field(&mut image, facts.architecture().as_bytes());
    for name in PLATFORM_SYSCTLS {
        let part = match (IMAGE_SYSCTLS.contains(name), BINDING_SYSCTLS.contains(name)) {
            (true, false) => &mut image,
            (false, true) => &mut binding,
            _ => bail!("platform sysctl {name} is not placed in exactly one part"),
        };
        field(part, name.as_bytes());
        match facts.sysctl(name)? {
            Some(value) => {
                field(part, b"present");
                field(part, &value);
            }
            None => field(part, b"absent"),
        }
    }
    for required in ["kern.bootsessionuuid", "kern.osversion"] {
        if facts.sysctl(required)?.is_none_or(|value| value.is_empty()) {
            bail!("required platform input is unavailable: {required}");
        }
    }
    field(&mut image, &facts.shared_cache_uuid()?);
    for path in PLATFORM_READ_FILES {
        let bytes = facts.file(std::path::Path::new(path), PLATFORM_FILE_LIMIT)?;
        if bytes.len() as u64 > PLATFORM_FILE_LIMIT {
            bail!("platform file exceeds its bound: {path}");
        }
        field(&mut image, path.as_bytes());
        field(&mut image, &bytes);
    }
    for (path, mount) in mounts {
        field(&mut binding, path.as_bytes());
        field(&mut binding, &mount);
    }
    Ok(PlatformInputs {
        image: image.finish_hex(),
        binding: binding.finish_hex(),
    })
}

/// Refuse a platform path unless its volume is sealed and mounted as the
/// read-only root snapshot; otherwise return its mount identity, which
/// belongs to the local binding.
#[cfg(target_os = "macos")]
fn sealed_snapshot_mount(facts: &dyn PlatformFacts, path: &std::path::Path) -> Result<Vec<u8>> {
    let volume = facts.volume(path)?;
    let required = (libc::MNT_RDONLY | libc::MNT_SNAPSHOT | libc::MNT_ROOTFS) as u32;
    if volume.mount_flags & required != required {
        bail!(
            "platform input is not on the read-only root snapshot: {}",
            path.display()
        );
    }
    let sealed = libc::VOL_CAP_FMT_SEALED;
    if volume.format_valid & sealed != sealed || volume.format_capabilities & sealed != sealed {
        bail!(
            "platform input is not on a cryptographically sealed system volume: {}",
            path.display()
        );
    }
    let mut value = Vec::new();
    value.extend_from_slice(&volume.device.to_le_bytes());
    for bytes in [&volume.filesystem, &volume.mounted_from, &volume.canonical] {
        value.extend_from_slice(&(bytes.len() as u64).to_le_bytes());
        value.extend_from_slice(bytes);
    }
    Ok(value)
}

/// The Mac this process runs on.
#[cfg(target_os = "macos")]
struct LocalMac;

#[cfg(target_os = "macos")]
impl PlatformFacts for LocalMac {
    fn architecture(&self) -> &str {
        std::env::consts::ARCH
    }

    fn sysctl(&self, name: &str) -> Result<Option<Vec<u8>>> {
        let name = std::ffi::CString::new(name)?;
        let mut size = 0;
        // SAFETY: both calls are read-only; the second owns a buffer of the exact
        // reported size. The kernel may not write beyond its in/out size argument.
        let result = unsafe {
            libc::sysctlbyname(
                name.as_ptr(),
                std::ptr::null_mut(),
                &mut size,
                std::ptr::null_mut(),
                0,
            )
        };
        if result != 0 {
            let error = std::io::Error::last_os_error();
            if error.raw_os_error() == Some(libc::ENOENT) {
                return Ok(None);
            }
            return Err(error.into());
        }
        if size > 4096 {
            bail!("platform sysctl value exceeds its bound");
        }
        let mut bytes = vec![0_u8; size];
        let result = unsafe {
            libc::sysctlbyname(
                name.as_ptr(),
                bytes.as_mut_ptr().cast(),
                &mut size,
                std::ptr::null_mut(),
                0,
            )
        };
        if result != 0 {
            return Err(std::io::Error::last_os_error().into());
        }
        if size > bytes.len() {
            bail!("platform sysctl value grew during capture");
        }
        bytes.truncate(size);
        Ok(Some(bytes))
    }

    fn shared_cache_uuid(&self) -> Result<[u8; 16]> {
        type Query = unsafe extern "C" fn(*mut u8) -> bool;
        // SAFETY: dyld exports this process-local query with the signature above.
        // Resolve it at runtime so an unavailable OS API fails closed, not at load.
        let address =
            unsafe { libc::dlsym(libc::RTLD_DEFAULT, c"_dyld_get_shared_cache_uuid".as_ptr()) };
        if address.is_null() {
            bail!("dyld shared-cache identity is unavailable");
        }
        let query: Query = unsafe { std::mem::transmute(address) };
        let mut uuid = [0; 16];
        if !unsafe { query(uuid.as_mut_ptr()) } || uuid == [0; 16] {
            bail!("dyld did not identify its loaded shared cache");
        }
        Ok(uuid)
    }

    fn file(&self, path: &std::path::Path, limit: u64) -> Result<Vec<u8>> {
        use std::io::Read;
        let mut bytes = Vec::new();
        std::fs::File::open(path)?
            .take(limit + 1)
            .read_to_end(&mut bytes)?;
        Ok(bytes)
    }

    fn volume(&self, path: &std::path::Path) -> Result<PlatformVolume> {
        use std::os::unix::{ffi::OsStrExt, fs::MetadataExt};
        let path = path.canonicalize()?;
        let name = std::ffi::CString::new(path.as_os_str().as_bytes())?;
        let mut mount = std::mem::MaybeUninit::<libc::statfs>::zeroed();
        // SAFETY: statfs owns an initialized, correctly sized output object.
        if unsafe { libc::statfs(name.as_ptr(), mount.as_mut_ptr()) } != 0 {
            return Err(std::io::Error::last_os_error().into());
        }
        let mount = unsafe { mount.assume_init() };
        let text = |buffer: &[libc::c_char]| -> Result<Vec<u8>> {
            let end = buffer
                .iter()
                .position(|byte| *byte == 0)
                .ok_or_else(|| anyhow::anyhow!("unterminated platform mount identity"))?;
            Ok(buffer[..end].iter().map(|byte| *byte as u8).collect())
        };

        #[repr(C)]
        struct Capabilities {
            length: u32,
            capabilities: libc::vol_capabilities_attr_t,
        }
        let mut request = libc::attrlist {
            bitmapcount: libc::ATTR_BIT_MAP_COUNT,
            reserved: 0,
            commonattr: 0,
            volattr: libc::ATTR_VOL_INFO | libc::ATTR_VOL_CAPABILITIES,
            dirattr: 0,
            fileattr: 0,
            forkattr: 0,
        };
        let mut reply = std::mem::MaybeUninit::<Capabilities>::zeroed();
        // SAFETY: getattrlist writes at most the given size into the reply,
        // which is zero-initialized and sized for the one requested attribute.
        if unsafe {
            libc::getattrlist(
                name.as_ptr(),
                (&raw mut request).cast(),
                reply.as_mut_ptr().cast(),
                std::mem::size_of::<Capabilities>(),
                0,
            )
        } != 0
        {
            return Err(std::io::Error::last_os_error().into());
        }
        let reply = unsafe { reply.assume_init() };
        if (reply.length as usize) < std::mem::size_of::<Capabilities>() {
            bail!(
                "volume capabilities of a platform input are incomplete: {}",
                path.display()
            );
        }
        let format = libc::VOL_CAPABILITIES_FORMAT;
        Ok(PlatformVolume {
            canonical: path.as_os_str().as_bytes().to_vec(),
            mount_flags: mount.f_flags,
            format_capabilities: reply.capabilities.capabilities[format],
            format_valid: reply.capabilities.valid[format],
            device: std::fs::metadata(&path)?.dev(),
            filesystem: text(&mount.f_fstypename)?,
            mounted_from: text(&mount.f_mntfromname)?,
        })
    }
}

#[cfg(all(test, target_os = "macos"))]
mod tests {
    use super::*;
    use std::collections::BTreeMap;
    use std::path::{Path, PathBuf};

    /// Facts a test controls, read through the production capture.
    #[derive(Clone)]
    struct Fixture {
        architecture: String,
        sysctls: BTreeMap<&'static str, Option<Vec<u8>>>,
        shared_cache: [u8; 16],
        files: BTreeMap<PathBuf, Vec<u8>>,
        volumes: BTreeMap<PathBuf, PlatformVolume>,
    }

    impl Fixture {
        fn mac() -> Self {
            let flags = (libc::MNT_RDONLY | libc::MNT_SNAPSHOT | libc::MNT_ROOTFS) as u32;
            Fixture {
                architecture: "aarch64".into(),
                sysctls: PLATFORM_SYSCTLS
                    .iter()
                    .map(|name| (*name, Some(format!("value of {name}").into_bytes())))
                    .collect(),
                shared_cache: [7; 16],
                files: PLATFORM_READ_FILES
                    .iter()
                    .map(|path| (PathBuf::from(path), b"<plist>27.2</plist>".to_vec()))
                    .collect(),
                volumes: PLATFORM_READ_DIRECTORIES
                    .iter()
                    .chain(PLATFORM_READ_FILES)
                    .map(|path| {
                        let volume = PlatformVolume {
                            canonical: path.as_bytes().to_vec(),
                            mount_flags: flags,
                            format_capabilities: libc::VOL_CAP_FMT_SEALED,
                            format_valid: libc::VOL_CAP_FMT_SEALED,
                            device: 0x1000004,
                            filesystem: b"apfs".to_vec(),
                            mounted_from: b"/dev/disk3s1s1".to_vec(),
                        };
                        (PathBuf::from(path), volume)
                    })
                    .collect(),
            }
        }

        fn varied(&self, change: impl FnOnce(&mut Fixture)) -> Fixture {
            let mut facts = self.clone();
            change(&mut facts);
            facts
        }
    }

    impl PlatformFacts for Fixture {
        fn architecture(&self) -> &str {
            &self.architecture
        }
        fn sysctl(&self, name: &str) -> Result<Option<Vec<u8>>> {
            Ok(self.sysctls.get(name).cloned().flatten())
        }
        fn shared_cache_uuid(&self) -> Result<[u8; 16]> {
            Ok(self.shared_cache)
        }
        fn file(&self, path: &Path, limit: u64) -> Result<Vec<u8>> {
            let bytes = &self.files[path];
            Ok(bytes[..bytes.len().min(limit as usize + 1)].to_vec())
        }
        fn volume(&self, path: &Path) -> Result<PlatformVolume> {
            Ok(self.volumes[path].clone())
        }
    }

    fn roots() -> impl Iterator<Item = PathBuf> {
        PLATFORM_READ_DIRECTORIES
            .iter()
            .chain(PLATFORM_READ_FILES)
            .map(PathBuf::from)
    }

    /// An image fact moves the key, keeps the binding, and fails currency.
    fn assert_image_fact(base: &Fixture, fact: &str, change: impl FnOnce(&mut Fixture)) {
        let before = capture_from(base).unwrap();
        let facts = base.varied(change);
        let after = capture_from(&facts).unwrap();
        assert_ne!(
            after.digest(),
            before.digest(),
            "{fact} must change the image"
        );
        assert_eq!(
            after.binding(),
            before.binding(),
            "{fact} is not a binding fact"
        );
        let error = before.ensure_current_from(&facts).unwrap_err();
        assert_eq!(
            error.to_string(),
            "confined action platform image changed",
            "{fact}"
        );
    }

    /// A binding fact keeps the key, moves the binding, and fails currency.
    fn assert_binding_fact(base: &Fixture, fact: &str, change: impl FnOnce(&mut Fixture)) {
        let before = capture_from(base).unwrap();
        let facts = base.varied(change);
        let after = capture_from(&facts).unwrap();
        assert_eq!(
            after.digest(),
            before.digest(),
            "{fact} must not change the image"
        );
        assert_ne!(
            after.binding(),
            before.binding(),
            "{fact} must change the binding"
        );
        let error = before.ensure_current_from(&facts).unwrap_err();
        assert_eq!(
            error.to_string(),
            "confined action local platform binding changed",
            "{fact}"
        );
    }

    fn assert_refused(facts: &Fixture, fact: &str, message: &str) {
        let error = capture_from(facts).unwrap_err().to_string();
        assert!(error.contains(message), "{fact}: {error}");
    }

    #[test]
    fn unchanged_facts_are_current() {
        let base = Fixture::mac();
        let inputs = capture_from(&base).unwrap();
        assert_eq!(inputs.digest().len(), 64);
        assert_eq!(inputs.binding().len(), 64);
        assert_ne!(inputs.digest(), inputs.binding());
        inputs.ensure_current_from(&base.clone()).unwrap();
    }

    #[test]
    fn every_permitted_sysctl_is_in_exactly_one_part() {
        for name in PLATFORM_SYSCTLS {
            assert!(
                IMAGE_SYSCTLS.contains(name) != BINDING_SYSCTLS.contains(name),
                "{name} must be in exactly one part"
            );
        }
        for name in IMAGE_SYSCTLS.iter().chain(BINDING_SYSCTLS) {
            assert!(PLATFORM_SYSCTLS.contains(name), "{name} is not permitted");
        }
        assert_eq!(
            IMAGE_SYSCTLS.len() + BINDING_SYSCTLS.len(),
            PLATFORM_SYSCTLS.len()
        );
    }

    #[test]
    fn each_image_sysctl_keys_the_digest() {
        let base = Fixture::mac();
        for &name in IMAGE_SYSCTLS {
            assert_image_fact(&base, name, |facts| {
                facts.sysctls.insert(name, Some(b"another image".to_vec()));
            });
            if name != "kern.osversion" {
                assert_image_fact(&base, name, |facts| {
                    facts.sysctls.insert(name, None);
                });
            }
        }
    }

    #[test]
    fn each_image_fact_outside_sysctl_keys_the_digest() {
        let base = Fixture::mac();
        assert_image_fact(&base, "architecture", |facts| {
            facts.architecture = "x86_64".into();
        });
        assert_image_fact(&base, "dyld shared cache", |facts| {
            facts.shared_cache = [8; 16];
        });
        for path in PLATFORM_READ_FILES {
            assert_image_fact(&base, path, |facts| {
                facts
                    .files
                    .insert(PathBuf::from(path), b"<plist>27.3</plist>".to_vec());
            });
        }
    }

    #[test]
    fn each_binding_sysctl_is_compared_but_not_keyed() {
        let base = Fixture::mac();
        for &name in BINDING_SYSCTLS {
            assert_binding_fact(&base, name, |facts| {
                facts.sysctls.insert(name, Some(b"another boot".to_vec()));
            });
            if name != "kern.bootsessionuuid" {
                assert_binding_fact(&base, name, |facts| {
                    facts.sysctls.insert(name, None);
                });
            }
        }
    }

    #[test]
    fn each_mount_identity_is_compared_but_not_keyed() {
        let base = Fixture::mac();
        for root in roots() {
            let fact = root.display().to_string();
            assert_binding_fact(&base, &fact, |facts| {
                facts.volumes.get_mut(&root).unwrap().device += 1;
            });
            assert_binding_fact(&base, &fact, |facts| {
                facts.volumes.get_mut(&root).unwrap().mounted_from = b"/dev/disk5s1s1".to_vec();
            });
            assert_binding_fact(&base, &fact, |facts| {
                facts.volumes.get_mut(&root).unwrap().filesystem = b"apfs2".to_vec();
            });
            assert_binding_fact(&base, &fact, |facts| {
                facts
                    .volumes
                    .get_mut(&root)
                    .unwrap()
                    .canonical
                    .extend_from_slice(b"/moved");
            });
        }
    }

    #[test]
    fn required_facts_must_be_present_and_nonempty() {
        let base = Fixture::mac();
        for name in ["kern.osversion", "kern.bootsessionuuid"] {
            for value in [None, Some(Vec::new())] {
                let facts = base.varied(|facts| {
                    facts.sysctls.insert(name, value);
                });
                assert_refused(&facts, name, "required platform input is unavailable");
            }
        }
    }

    #[test]
    fn unsealed_or_writable_roots_refuse() {
        let base = Fixture::mac();
        for root in roots() {
            let fact = root.display().to_string();
            for flag in [libc::MNT_RDONLY, libc::MNT_SNAPSHOT, libc::MNT_ROOTFS] {
                let facts = base.varied(|facts| {
                    facts.volumes.get_mut(&root).unwrap().mount_flags &= !(flag as u32);
                });
                assert_refused(&facts, &fact, "not on the read-only root snapshot");
            }
            let unsealed = base.varied(|facts| {
                facts.volumes.get_mut(&root).unwrap().format_capabilities = 0;
            });
            assert_refused(&unsealed, &fact, "not on a cryptographically sealed");
            let unknown = base.varied(|facts| {
                facts.volumes.get_mut(&root).unwrap().format_valid = 0;
            });
            assert_refused(&unknown, &fact, "not on a cryptographically sealed");
            // A root that becomes unsealed after capture fails currency too.
            let before = capture_from(&base).unwrap();
            assert!(before.ensure_current_from(&unsealed).is_err());
        }
    }

    #[test]
    fn an_oversized_system_version_file_refuses() {
        let base = Fixture::mac();
        let facts = base.varied(|facts| {
            for path in PLATFORM_READ_FILES {
                facts.files.insert(
                    PathBuf::from(path),
                    vec![b'x'; PLATFORM_FILE_LIMIT as usize + 1],
                );
            }
        });
        assert_refused(&facts, "SystemVersion.plist", "exceeds its bound");
    }

    #[test]
    fn this_mac_has_a_current_sealed_platform() {
        let inputs = PlatformInputs::capture().unwrap();
        assert_eq!(inputs.digest().len(), 64);
        assert_eq!(inputs.binding().len(), 64);
        inputs.ensure_current().unwrap();
        assert_ne!(LocalMac.shared_cache_uuid().unwrap(), [0; 16]);
        for root in roots() {
            let volume = LocalMac.volume(&root).unwrap();
            assert_ne!(
                volume.format_capabilities & libc::VOL_CAP_FMT_SEALED,
                0,
                "{root:?}"
            );
        }
    }

    #[test]
    fn writable_storage_cannot_supply_an_immutable_platform_identity() {
        let root = tempfile::tempdir().unwrap();
        assert!(sealed_snapshot_mount(&LocalMac, root.path()).is_err());
    }
}
