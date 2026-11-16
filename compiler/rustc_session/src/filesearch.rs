//! A module for searching for libraries

use std::path::{Path, PathBuf};
use std::sync::Arc;
use std::{env, fs, iter};

use rustc_fs_util::try_canonicalize;
use rustc_target::spec::Target;

use crate::search_paths::{PathKind, SearchPath};

pub struct FileSearch {
    cli_search_paths: Vec<SearchPath>,
    tlib_path: SearchPath,
    // Trust: compiler helpers sharing a name with std are dependency-only.
    sysroot_dependency_path: Option<SearchPath>,
    use_implicit_sysroot_deps: bool,
    files: Vec<FileSearchCandidate>,
}

impl FileSearch {
    pub fn cli_search_paths<'b>(&'b self, kind: PathKind) -> impl Iterator<Item = &'b SearchPath> {
        self.cli_search_paths.iter().filter(move |sp| sp.kind.matches(kind))
    }

    pub fn search_paths<'b>(&'b self, kind: PathKind) -> impl Iterator<Item = &'b SearchPath> {
        // If the crate is `PathKind::Crate` (a top level dependency)
        // and `-Z implicit-sysroot-deps=false`, then don't include the sysroot in the search paths.
        let exclude_sysroot = kind.matches(PathKind::Crate) && !self.use_implicit_sysroot_deps;
        let maybe_tlib = (!exclude_sysroot).then_some(&self.tlib_path);

        self.cli_search_paths
            .iter()
            .filter(move |sp| sp.kind.matches(kind))
            .chain(maybe_tlib.into_iter())
            .chain(
                self.sysroot_dependency_path
                    .iter()
                    .filter(move |sp| !exclude_sysroot && sp.kind.matches(kind)),
            )
    }

    /// Return files from the search dirs of this filesearch that match the given `prefix` and
    /// `suffix` and have the given `kind`.
    ///
    /// Note that this function only searches files that match lib/staticlib/dlllib prefixes, not
    /// all files from the search paths!
    /// Access `search_paths` directly if you want to scan all files within them.
    pub fn get_library_candidates<'b>(
        &'b self,
        prefix: &'b str,
        suffix: &'b str,
        kind: PathKind,
    ) -> impl Iterator<Item = (&'b str, PathBuf)> {
        let exclude_sysroot = kind.matches(PathKind::Crate) && !self.use_implicit_sysroot_deps;

        // The indices are clipped to have only a single iterator returned from this function, to
        // avoid allocating it.
        let start = self.files.partition_point(|v| *v.filename < *prefix).min(self.files.len());
        let end = self.files[start..].partition_point(|v| v.filename.starts_with(prefix));
        let prefixed_items = &self.files[start..][..end];

        prefixed_items
            .into_iter()
            .filter(move |c| {
                c.kind.matches(kind)
                    && !(exclude_sysroot && c.from_sysroot)
                    && c.filename.ends_with(suffix)
            })
            .map(|c| (&c.filename[prefix.len()..c.filename.len() - suffix.len()], c.path()))
    }

    pub fn new(
        cli_search_paths: &[SearchPath],
        tlib_path: &SearchPath,
        target: &Target,
        use_implicit_sysroot_deps: bool,
    ) -> Self {
        // We keep a list of all found paths that look like libraries in `FileSearch`, to optimize
        // lookup in `get_library_candidates`.
        // These prefixes should be kept in sync with `CrateLocator::find_library_crate`.
        let staticlib_prefix = target.staticlib_prefix.as_ref();
        let dll_prefix = target.dll_prefix.as_ref();
        let check_staticlib_prefix = staticlib_prefix != "lib";
        let check_dll_prefix = dll_prefix != "lib" && dll_prefix != staticlib_prefix;

        // Trust: bootstrap retains the compiler's other versions of std helper
        // crates here. They must resolve by dependency hash without competing
        // with a bare `extern crate libc`/`hashbrown` in the public sysroot.
        let dependency_dir = tlib_path.dir.join("rustc-dependencies");
        let sysroot_dependency_path = dependency_dir
            .is_dir()
            .then(|| SearchPath { kind: PathKind::Dependency, dir: dependency_dir.into() });

        // Load all files from all search paths, filter them by supported prefixes, and sort them,
        // so that we can efficiently look them up in `get_file_candidates` via binary search.
        let mut files: Vec<FileSearchCandidate> = Vec::with_capacity(cli_search_paths.len());
        for (search_path, is_sysroot) in cli_search_paths
            .iter()
            .map(|path| (path, false))
            .chain(iter::once((tlib_path, true)))
            .chain(sysroot_dependency_path.iter().map(|path| (path, true)))
        {
            let Ok(dir) = fs::read_dir(&search_path.dir) else {
                continue;
            };
            files.extend(dir.filter_map(|entry| {
                let entry = entry.ok()?;

                let filename = entry.file_name();
                let filename = filename.to_str()?;

                if !filename.starts_with("lib")
                    && (!check_staticlib_prefix || !filename.starts_with(staticlib_prefix))
                    && (!check_dll_prefix || !filename.starts_with(dll_prefix))
                {
                    return None;
                }
                Some(FileSearchCandidate {
                    dir: Arc::clone(&search_path.dir),
                    filename: filename.into(),
                    kind: search_path.kind,
                    from_sysroot: is_sysroot,
                })
            }));
        }
        files.sort_unstable_by(|lhs, rhs| lhs.filename.cmp(&rhs.filename));

        FileSearch {
            cli_search_paths: cli_search_paths.to_owned(),
            tlib_path: tlib_path.clone(),
            sysroot_dependency_path,
            use_implicit_sysroot_deps,
            files,
        }
    }
}

/// This type stores `Box<str>` instead of `PathBuf` for the filename, because getting the
/// `file_name` of a `PathBuf` allocates, which is unnecessary. We have to go through the files
/// a lot of times, so storing file name and the directory separately saves time and memory.
///
/// The filename must be valid UTF-8. If it's not, the entry should be skipped, because all Rust
/// output files are valid UTF-8, and so a non-UTF-8 filename couldn't be one we're looking for.
#[derive(Debug)]
struct FileSearchCandidate {
    dir: Arc<Path>,
    filename: Box<str>,
    kind: PathKind,
    /// Was this file added through the target sysroot?
    from_sysroot: bool,
}

impl FileSearchCandidate {
    /// Constructs the full path to the file.
    fn path(&self) -> PathBuf {
        self.dir.join(&*self.filename)
    }
}

pub fn make_target_lib_path(sysroot: &Path, target_triple: &str) -> PathBuf {
    let rustlib_path = rustc_target::relative_target_rustlib_path(sysroot, target_triple);
    sysroot.join(rustlib_path).join("lib")
}

/// Returns a path to the target's `bin` folder within its `rustlib` path in the sysroot. This is
/// where binaries are usually installed, e.g. the self-contained linkers, lld-wrappers, LLVM tools,
/// etc.
pub fn make_target_bin_path(sysroot: &Path, target_triple: &str) -> PathBuf {
    let rustlib_path = rustc_target::relative_target_rustlib_path(sysroot, target_triple);
    sysroot.join(rustlib_path).join("bin")
}

// Trust: exercise the actual search/candidate APIs with both crate populations.
#[cfg(test)]
#[path = "filesearch/tests.rs"]
mod trust_dependency_tests;

/// Attempts to find the path to the dynamic library containing a function.
///
/// SAFETY: `function` must be a valid pointer to some function.
#[cfg(unix)]
pub unsafe fn dll_path(function: *mut std::ffi::c_void) -> Result<PathBuf, String> {
    use std::ffi::{CStr, OsStr};
    use std::os::unix::prelude::*;

    #[cfg(not(target_os = "aix"))]
    unsafe {
        let mut info = std::mem::zeroed();
        if libc::dladdr(function, &mut info) == 0 {
            return Err("dladdr failed".into());
        }
        #[cfg(target_os = "cygwin")]
        let fname_ptr = info.dli_fname.as_ptr();
        #[cfg(not(target_os = "cygwin"))]
        let fname_ptr = {
            assert!(!info.dli_fname.is_null(), "dli_fname cannot be null");
            info.dli_fname
        };
        let bytes = CStr::from_ptr(fname_ptr).to_bytes();
        let os = OsStr::from_bytes(bytes);
        try_canonicalize(Path::new(os)).map_err(|e| e.to_string())
    }

    #[cfg(target_os = "aix")]
    unsafe {
        // On AIX, the symbol references a function descriptor.
        // A function descriptor is consisted of (See https://reviews.llvm.org/D62532)
        // * The address of the entry point of the function.
        // * The TOC base address for the function.
        // * The environment pointer.
        // The function descriptor is in the data section.
        let addr = function as u64;
        let mut buffer = vec![std::mem::zeroed::<libc::ld_info>(); 64];
        loop {
            if libc::loadquery(
                libc::L_GETINFO,
                buffer.as_mut_ptr() as *mut libc::c_void,
                (size_of::<libc::ld_info>() * buffer.len()) as u32,
            ) >= 0
            {
                break;
            } else {
                if std::io::Error::last_os_error().raw_os_error().unwrap() != libc::ENOMEM {
                    return Err("loadquery failed".into());
                }
                buffer.resize(buffer.len() * 2, std::mem::zeroed::<libc::ld_info>());
            }
        }
        let mut current = buffer.as_mut_ptr() as *mut libc::ld_info;
        loop {
            let data_base = (*current).ldinfo_dataorg as u64;
            let data_end = data_base + (*current).ldinfo_datasize;
            if (data_base..data_end).contains(&addr) {
                let bytes = CStr::from_ptr(&(*current).ldinfo_filename[0]).to_bytes();
                let os = OsStr::from_bytes(bytes);
                return try_canonicalize(Path::new(os)).map_err(|e| e.to_string());
            }
            if (*current).ldinfo_next == 0 {
                break;
            }
            current =
                (current as *mut i8).offset((*current).ldinfo_next as isize) as *mut libc::ld_info;
        }
        return Err(format!("current dll's address {} is not in the load map", addr));
    }
}

#[cfg(windows)]
pub unsafe fn dll_path(function: *mut std::ffi::c_void) -> Result<PathBuf, String> {
    use std::ffi::OsString;
    use std::io;
    use std::os::windows::prelude::*;

    use windows::Win32::Foundation::HMODULE;
    use windows::Win32::System::LibraryLoader::{
        GET_MODULE_HANDLE_EX_FLAG_FROM_ADDRESS, GetModuleFileNameW, GetModuleHandleExW,
    };
    use windows::core::PCWSTR;

    let mut module = HMODULE::default();
    unsafe {
        GetModuleHandleExW(
            GET_MODULE_HANDLE_EX_FLAG_FROM_ADDRESS,
            PCWSTR(function as *mut u16),
            &mut module,
        )
    }
    .map_err(|e| e.to_string())?;

    let mut filename = vec![0; 1024];
    let n = unsafe { GetModuleFileNameW(Some(module), &mut filename) } as usize;
    if n == 0 {
        return Err(format!("GetModuleFileNameW failed: {}", io::Error::last_os_error()));
    }
    if n >= filename.capacity() {
        return Err(format!("our buffer was too small? {}", io::Error::last_os_error()));
    }

    filename.truncate(n);

    let path = try_canonicalize(OsString::from_wide(&filename)).map_err(|e| e.to_string())?;

    // See comments on this target function, but the gist is that
    // gcc chokes on verbatim paths which fs::canonicalize generates
    // so we try to avoid those kinds of paths.
    Ok(rustc_fs_util::fix_windows_verbatim_for_gcc(&path))
}

#[cfg(target_os = "wasi")]
pub unsafe fn dll_path(_function: *mut std::ffi::c_void) -> Result<PathBuf, String> {
    Err("dll_path is not supported on WASI".to_string())
}

// Trust (TG6): public, so the compiler can name the image its Clean checker
// runs from (a local kernel fact's compiler identity); trust-certify forbids the
// `unsafe` a loader query needs.
pub fn current_dll_path() -> Result<PathBuf, String> {
    use std::sync::OnceLock;

    // This is somewhat expensive relative to other work when compiling `fn main() {}` as `dladdr`
    // needs to iterate over the symbol table of librustc_driver.so until it finds a match.
    // As such cache this to avoid recomputing if we try to get the sysroot in multiple places.
    static CURRENT_DLL_PATH: OnceLock<Result<PathBuf, String>> = OnceLock::new();
    CURRENT_DLL_PATH
        .get_or_init(|| unsafe { dll_path(current_dll_path as fn() -> _ as *mut _) })
        .clone()
}

// Trust (TG6): the file the compiler's own code is mapped from, as the kernel
// reports it, so a local kernel fact's compiler identity is the image this
// process runs. The path `current_dll_path` names can be another file by the
// time the compiler first opens its facts (a toolchain rebuilt at the same
// commit unlinks the old driver and writes the new one under its name while
// processes that loaded the old one still run); a caller opens that path and
// accepts the file only when its device and inode are these.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct MappedFile {
    /// `st_dev` of the mapped file, as `std::os::unix::fs::MetadataExt::dev`.
    pub device: u64,
    /// `st_ino` of the mapped file, as `std::os::unix::fs::MetadataExt::ino`.
    pub inode: u64,
}

// Trust (TG6): `current_dll_path` and the kernel's account of the file mapped
// at it (see `MappedFile`). Hosts with no such account (every one but macOS,
// Linux and Android) get an error, and so no compiler identity.
pub fn current_dll_mapping() -> Result<(PathBuf, MappedFile), String> {
    use std::sync::OnceLock;

    static MAPPING: OnceLock<Result<MappedFile, String>> = OnceLock::new();
    let path = current_dll_path()?;
    let mapping = MAPPING
        .get_or_init(|| {
            mapped_file_of(current_dll_path as fn() -> Result<PathBuf, String> as usize)
        })
        .clone()?;
    Ok((path, mapping))
}

// Trust (TG6): the device and inode of the file the region holding `address`
// is mapped from, by `proc_pidinfo(PROC_PIDREGIONPATHINFO)`.
#[cfg(target_os = "macos")]
fn mapped_file_of(address: usize) -> Result<MappedFile, String> {
    use std::mem::{MaybeUninit, offset_of};

    // `struct proc_regioninfo` of <sys/proc_info.h>, which `libc` lacks: its
    // flags and counters, then the region's address and size.
    #[repr(C)]
    struct RegionInfo {
        _flags: [u32; 4],
        _offset: u64,
        _counters: [u32; 14],
        address: u64,
        size: u64,
    }
    // `struct proc_regionwithpathinfo`.
    #[repr(C)]
    struct RegionWithPathInfo {
        region: RegionInfo,
        vnode: libc::vnode_info_path,
    }
    const PROC_PIDREGIONPATHINFO: libc::c_int = 8;
    // The SDK's layout (measured with its headers, 2026-11-06).
    const _: () = assert!(
        size_of::<RegionInfo>() == 96
            && offset_of!(RegionInfo, address) == 80
            && size_of::<RegionWithPathInfo>() == 1272
    );

    let size = size_of::<RegionWithPathInfo>() as libc::c_int;
    let mut info = MaybeUninit::<RegionWithPathInfo>::zeroed();
    // SAFETY: `info` is `size` writable bytes laid out as the kernel writes
    // them for this flavor (asserted above).
    let written = unsafe {
        libc::proc_pidinfo(
            libc::getpid(),
            PROC_PIDREGIONPATHINFO,
            address as u64,
            info.as_mut_ptr().cast(),
            size,
        )
    };
    if written != size {
        return Err(format!(
            "proc_pidinfo(PROC_PIDREGIONPATHINFO) failed: {}",
            std::io::Error::last_os_error()
        ));
    }
    // SAFETY: the kernel wrote all `size` bytes, and every field is plain data
    // for which any bytes are a value (the buffer started zeroed besides).
    let info = unsafe { info.assume_init() };
    let address = address as u64;
    if !(info.region.address <= address && address - info.region.address < info.region.size) {
        return Err("the region the kernel reported does not hold the compiler's code".into());
    }
    let stat = info.vnode.vip_vi.vi_stat;
    if stat.vst_ino == 0 {
        return Err("the compiler's code is not mapped from a file".into());
    }
    // `dev_t` is `i32` here; widen it as `MetadataExt::dev` does.
    Ok(MappedFile { device: stat.vst_dev as libc::dev_t as u64, inode: stat.vst_ino })
}

// Trust (TG6): the device and inode of the file the region holding `address`
// is mapped from, by `/proc/self/maps`.
#[cfg(any(target_os = "linux", target_os = "android"))]
fn mapped_file_of(address: usize) -> Result<MappedFile, String> {
    let maps = fs::read_to_string("/proc/self/maps")
        .map_err(|error| format!("/proc/self/maps: {error}"))?;
    let (major, minor, inode) = proc_maps_file(&maps, address)
        .ok_or_else(|| "/proc/self/maps maps no file at the compiler's code".to_string())?;
    Ok(MappedFile { device: libc::makedev(major, minor) as u64, inode })
}

#[cfg(not(any(target_os = "macos", target_os = "linux", target_os = "android")))]
fn mapped_file_of(_address: usize) -> Result<MappedFile, String> {
    Err("this host reports no file a compiler's code is mapped from".into())
}

// Trust (TG6): the device numbers and inode of the `/proc/<pid>/maps` line
// whose range holds `address` (`start-end perms offset major:minor inode
// path`, all in hex but the inode), when that line maps a file.
#[cfg(any(target_os = "linux", target_os = "android", test))]
fn proc_maps_file(maps: &str, address: usize) -> Option<(u32, u32, u64)> {
    maps.lines().find_map(|line| {
        let mut fields = line.split_ascii_whitespace();
        let (start, end) = fields.next()?.split_once('-')?;
        let start = usize::from_str_radix(start, 16).ok()?;
        let end = usize::from_str_radix(end, 16).ok()?;
        if !(start..end).contains(&address) {
            return None;
        }
        let (_permissions, _offset) = (fields.next()?, fields.next()?);
        let (major, minor) = fields.next()?.split_once(':')?;
        let inode: u64 = fields.next()?.parse().ok()?;
        if inode == 0 {
            return None;
        }
        Some((u32::from_str_radix(major, 16).ok()?, u32::from_str_radix(minor, 16).ok()?, inode))
    })
}

/// This function checks if sysroot is found using env::args().next(), and if it
/// is not found, finds sysroot from current rustc_driver dll.
pub(crate) fn default_sysroot() -> PathBuf {
    fn default_from_rustc_driver_dll() -> Result<PathBuf, String> {
        let dll = current_dll_path()?;

        // `dll` will be in one of the following two:
        // - compiler's libdir: $sysroot/lib/*.dll
        // - target's libdir: $sysroot/lib/rustlib/$target/lib/*.dll
        //
        // use `parent` twice to chop off the file name and then also the
        // directory containing the dll
        let dir = dll.parent().and_then(|p| p.parent()).ok_or_else(|| {
            format!("Could not move 2 levels upper using `parent()` on {}", dll.display())
        })?;

        // if `dir` points to target's dir, move up to the sysroot
        let mut sysroot_dir = if dir.ends_with(crate::config::host_tuple()) {
            dir.parent() // chop off `$target`
                .and_then(|p| p.parent()) // chop off `rustlib`
                .and_then(|p| p.parent()) // chop off `lib`
                .map(|s| s.to_owned())
                .ok_or_else(|| {
                    format!("Could not move 3 levels upper using `parent()` on {}", dir.display())
                })?
        } else {
            dir.to_owned()
        };

        // On multiarch linux systems, there will be multiarch directory named
        // with the architecture(e.g `x86_64-linux-gnu`) under the `lib` directory.
        // Which cause us to mistakenly end up in the lib directory instead of the sysroot directory.
        if sysroot_dir.ends_with("lib") {
            sysroot_dir =
                sysroot_dir.parent().map(|real_sysroot| real_sysroot.to_owned()).ok_or_else(
                    || format!("Could not move to parent path of {}", sysroot_dir.display()),
                )?
        }

        Ok(sysroot_dir)
    }

    // Use env::args().next() to get the path of the executable without
    // following symlinks/canonicalizing any component. This makes the rustc
    // binary able to locate Rust libraries in systems using content-addressable
    // storage (CAS).
    fn from_env_args_next() -> Option<PathBuf> {
        let mut p = PathBuf::from(env::args_os().next()?);

        // Check if sysroot is found using env::args().next() only if the rustc in argv[0]
        // is a symlink (see #79253). We might want to change/remove it to conform with
        // https://www.gnu.org/prep/standards/standards.html#Finding-Program-Files in the
        // future.
        if fs::read_link(&p).is_err() {
            // Path is not a symbolic link or does not exist.
            return None;
        }

        // Pop off `bin/rustc`, obtaining the suspected sysroot.
        p.pop();
        p.pop();
        // Look for the target rustlib directory in the suspected sysroot.
        let mut rustlib_path = rustc_target::relative_target_rustlib_path(&p, "dummy");
        rustlib_path.pop(); // pop off the dummy target.
        rustlib_path.exists().then_some(p)
    }

    from_env_args_next()
        .unwrap_or_else(|| default_from_rustc_driver_dll().expect("Failed finding sysroot"))
}
