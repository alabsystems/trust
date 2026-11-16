// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates

//! Original output-root and native program/runtime input custody. The host
//! creates the root owner before compiling and retains it across compiler and
//! foreign phases. It must independently establish compiler quiescence, actual
//! UnitOutput identity, SDK and CPU/GNU/memory authority before execution.
//! Opening these inputs proves no compilation, source identity or admission.

use std::sync::Arc;

use super::*;

mod evidence;
pub use evidence::{BoundedEvidenceFile, HeldEvidenceRoot};
mod data;
pub use data::HeldRootFile;
mod directory;
mod publication;
pub use directory::HeldRootDirectory;
pub use publication::PublicationExclusions;

pub const RUNTIME_POLICY: &str = "native-produced/macho-arm64-original-output-sdk-v1";

struct OutputBacking {
    path: PathBuf,
    file: File,
    before: Metadata,
    // Derived roots retain the original master-relative no-follow chain.
    ancestry: Option<HeldRootDirectory>,
    // LAST: native descriptor accounting outlives every retained original.
    retention: Option<Arc<dyn Send + Sync>>,
}
impl OutputBacking {
    fn validate(&self, deadline: Instant) -> io::Result<()> {
        if let Some(original) = &self.ancestry { original.validate(deadline)?; }
        let current = directory(&self.path, deadline)?;
        // A compiler may add outputs. That does not replace its original root
        // or permit changed ownership, permissions, ACLs or pathname routing.
        for file in [&self.file, &current] {
            if !same_directory(&self.before, &owned(file, true, false)?, false) {
                return Err(refused("original compiler output root changed"));
            }
        }
        Ok(())
    }
}

/// Non-cloneable original root description. Records and pathnames cannot
/// reconstruct this owner. Its presence alone grants no right to run a file.
pub struct HeldOutputRoot {
    backing: Arc<OutputBacking>,
}
impl HeldOutputRoot {
    pub fn open(root: &Path, deadline: Instant) -> io::Result<Self> {
        let file = directory(root, deadline)?;
        let before = owned(&file, true, false)?;
        let backing = Arc::new(OutputBacking {
            path: root.to_owned(),
            file,
            before,
            ancestry: None,
            retention: None,
        });
        backing.validate(deadline)?;
        Ok(Self { backing })
    }
    /// Continue a genuinely held child directory as a selected compilation
    /// root. The actual original master/ancestor FDs remain in this owner;
    /// no absolute-path reopen or saved identity constructs the selection.
    /// Reserve the additional description BEFORE this operation. It grants
    /// no writer, compiler, publication or resource authority by itself.
    pub fn from_original_directory(original: HeldRootDirectory, deadline: Instant) -> io::Result<Self> {
        original.validate(deadline)?;
        let path=original.path().to_owned();
        let file=File::from(original.descriptor(deadline)?.try_clone_to_owned()?);
        let before=owned(&file,true,false)?;
        let output=Self {backing:Arc::new(OutputBacking {path,file,before,ancestry:Some(original),retention:None})};
        output.validate(deadline)?; Ok(output)
    }
    /// Attach lifetime-only native accounting before sharing the newly held
    /// root. This can only extend retention of an already genuine original;
    /// it creates no admission, writer, materialization or execution grant.
    pub fn retain_descriptor_guard(mut self, guard: Arc<dyn Send + Sync>) -> io::Result<Self> {
        let backing=Arc::get_mut(&mut self.backing).ok_or_else(|| refused("selected output root was shared before descriptor accounting"))?;
        if backing.retention.is_some() { return Err(refused("selected output root already retains descriptor accounting")); }
        backing.retention=Some(guard); Ok(self)
    }
    pub fn derived_from(&self, master: &HeldOutputRoot) -> bool {
        self.backing.ancestry.as_ref().is_some_and(|directory| directory.belongs_to_root(master))
    }
    pub fn original_identity(&self, deadline:Instant) -> io::Result<(u64,u64)> {
        self.validate(deadline)?; Ok((self.backing.before.dev(),self.backing.before.ino()))
    }
    pub fn descriptor_count(&self) -> usize {
        1 + self.backing.ancestry.as_ref().map_or(0,HeldRootDirectory::descriptor_count)
    }
    pub fn path(&self) -> &Path {
        &self.backing.path
    }
    pub fn validate(&self, deadline: Instant) -> io::Result<()> {
        self.backing.validate(deadline)
    }
    /// Borrow the SAME held directory after its current native name/identity
    /// bookend. This creates no new description, writer, resource admission or
    /// completion authority; the caller must retain its actual output owners.
    pub fn descriptor(&self, deadline: Instant) -> io::Result<std::os::fd::BorrowedFd<'_>> {
        use std::os::fd::AsFd as _;
        self.validate(deadline)?;
        Ok(self.backing.file.as_fd())
    }

    /// Prepare bounded, create-only failure evidence before compilation. The
    /// attempt is a namespace, never an admission credential. Existing attempt
    /// directories are refused; older evidence is never reused or overwritten.
    pub fn open_with_evidence(
        root: &Path,
        sdk: &HeldProgram,
        attempt: [u8; 16],
        total_bytes: u64,
        file_limit: u32,
        deadline: Instant,
    ) -> io::Result<(Self, HeldEvidenceRoot)> {
        sdk.validate(deadline)?;
        canonical(root)?;
        if root.starts_with(sdk.root()) || sdk.root().starts_with(root) {
            return Err(refused("evidence output and original SDK must be disjoint"));
        }
        let output = Self::open(root, deadline)?;
        for marker in [".git", "Cargo.toml", "Targo.toml"] {
            match openat(output.backing.file.as_raw_fd(), OsStr::new(marker), false) {
                Ok(_) => {
                    return Err(refused(
                        "workload evidence cannot reclassify a source root as output",
                    ));
                }
                Err(error) if error.kind() == io::ErrorKind::NotFound => {}
                Err(error) => return Err(error),
            }
        }
        let evidence = evidence::prepare(
            Arc::clone(&output.backing),
            attempt,
            total_bytes,
            file_limit,
            deadline,
        )?;
        sdk.validate(deadline)?;
        Ok((output, evidence))
    }

    /// Capture actual native bytes after the custodian has positively retired
    /// all active compiler writers. The expected digest and runtime paths are
    /// equality inputs, never a build receipt or resource grant. The same
    /// original SDK and output descriptions remain held in the returned owner.
    pub fn program(
        &self,
        sdk: Arc<HeldProgram>,
        program: &Path,
        expected: &[u8; 32],
        runtime_roots: &[PathBuf],
        deadline: Instant,
    ) -> io::Result<HeldProducedProgram> {
        #[cfg(not(all(target_os = "macos", target_arch = "aarch64")))]
        {
            let _ = (sdk, program, expected, runtime_roots, deadline);
            Err(io::Error::new(
                io::ErrorKind::Unsupported,
                "native produced runtime profile unavailable",
            ))
        }
        #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
        {
            self.validate(deadline)?;
            sdk.validate(deadline)?;
            let inputs = capture(self.path(), &sdk, program, expected, runtime_roots, deadline)?;
            let held = HeldProducedProgram {
                output: Arc::clone(&self.backing),
                sdk,
                inputs,
                descriptor_guard: None,
            };
            held.validate(deadline)?;
            Ok(held)
        }
    }
}

/// Complete supported non-system native runtime held through actual scope
/// retirement. No public observation can recreate this value or authorize GO.
pub struct HeldProducedProgram {
    output: Arc<OutputBacking>,
    sdk: Arc<HeldProgram>,
    inputs: HeldProgram,
    // LAST: lifetime-only accounting survives every shared image owner.
    descriptor_guard: Option<Arc<dyn Send + Sync>>,
}
impl HeldProducedProgram {
    /// Attach an already admitted descriptor envelope before sharing this
    /// genuine image. This grants no native execution or producer authority.
    pub fn retain_descriptor_guard(mut self, guard: Arc<dyn Send + Sync>) -> io::Result<Self> {
        if self.descriptor_guard.is_some() {
            return Err(refused("produced image already retains descriptor accounting"));
        }
        self.descriptor_guard = Some(guard);
        Ok(self)
    }
    /// Owned image/loader metadata only; shared original SDK/output owners
    /// and file contents are not counted again. This performs no IO.
    pub fn retained_bytes(&self) -> Option<usize> {
        fn file(value: &FileObservation) -> Option<usize> {
            value.path.capacity().checked_add(value.sha256.capacity())
        }
        let inputs = &self.inputs;
        let mut bytes = std::mem::size_of::<Self>()
            .checked_add(inputs.root.capacity())?
            .checked_add(file(&inputs.executable.observation)?)?
            .checked_add(inputs.runtime.capacity().checked_mul(std::mem::size_of::<HeldFile>())?)?;
        for held in &inputs.runtime {
            bytes = bytes.checked_add(file(&held.observation)?)?;
        }
        for path in inputs.directories.keys() {
            bytes = bytes
                .checked_add(
                    std::mem::size_of::<(PathBuf, HeldDirectory)>()
                        .checked_mul(11)?
                        .checked_add(128)?,
                )?
                .checked_add(path.capacity())?;
        }
        let observation = &inputs.observation;
        bytes = bytes
            .checked_add(file(&observation.executable)?)?
            .checked_add(
                observation
                    .runtime
                    .capacity()
                    .checked_mul(std::mem::size_of::<FileObservation>())?,
            )?
            .checked_add(
                observation.loader_paths.capacity().checked_mul(std::mem::size_of::<PathBuf>())?,
            )?
            .checked_add(
                observation
                    .system_dependencies
                    .capacity()
                    .checked_mul(std::mem::size_of::<String>())?,
            )?
            .checked_add(observation.host.capacity())?
            .checked_add(observation.boot.capacity())?;
        for value in &observation.runtime {
            bytes = bytes.checked_add(file(value)?)?;
        }
        for path in &observation.loader_paths {
            bytes = bytes.checked_add(path.capacity())?;
        }
        for value in &observation.system_dependencies {
            bytes = bytes.checked_add(value.capacity())?;
        }
        Some(bytes)
    }
    pub fn observation(&self) -> &ProgramObservation {
        self.inputs.observation()
    }
    pub fn program(&self) -> &Path {
        self.inputs.program()
    }
    pub fn output_root(&self) -> &Path {
        &self.output.path
    }
    pub fn sdk_observation(&self) -> &ProgramObservation {
        self.sdk.observation()
    }
    pub fn sdk_root(&self) -> &Path {
        self.sdk.root()
    }
    /// Borrow the SAME originally held read-only executable for a separately
    /// authenticated live output registration. Revalidate the complete original
    /// output/SDK/runtime inputs first; never reopen a path as a replacement.
    /// The caller must retain this owner, its actual compilation/output leases
    /// and the host's independent phase admission through native retirement.
    /// A description transfer alone grants no execution or source authority.
    pub fn executable_descriptor(
        &self,
        deadline: Instant,
    ) -> io::Result<std::os::fd::BorrowedFd<'_>> {
        self.validate(deadline)?;
        Ok(std::os::fd::AsFd::as_fd(&self.inputs.executable.file))
    }
    pub fn runtime_environment(&self) -> io::Result<Vec<(OsString, OsString)>> {
        self.inputs.runtime_environment()
    }
    pub fn validate(&self, deadline: Instant) -> io::Result<()> {
        self.output.validate(deadline)?;
        self.sdk.validate(deadline)?;
        self.inputs.validate(deadline)
    }
    pub fn validate_loaded(&self, child: process::Identity, deadline: Instant) -> io::Result<()> {
        self.validate(deadline)?;
        self.inputs.validate_loaded(child, deadline)?;
        self.validate(deadline)
    }
}

#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
fn expand(value: &str, binary: &Path, executable: &Path) -> io::Result<PathBuf> {
    let expanded = if value == "@loader_path" {
        binary.parent().unwrap().to_owned()
    } else if let Some(tail) = value.strip_prefix("@loader_path/") {
        if tail.starts_with('/') {
            return Err(refused("produced loader suffix is absolute"));
        }
        binary.parent().unwrap().join(tail)
    } else if value == "@executable_path" {
        executable.parent().unwrap().to_owned()
    } else if let Some(tail) = value.strip_prefix("@executable_path/") {
        if tail.starts_with('/') {
            return Err(refused("produced executable suffix is absolute"));
        }
        executable.parent().unwrap().join(tail)
    } else if Path::new(value).is_absolute() {
        PathBuf::from(value)
    } else {
        return Err(refused("produced runtime path has no supported loader base"));
    };
    let mut normalized = PathBuf::new();
    for part in expanded.components() {
        match part {
            Component::RootDir | Component::Normal(_) => normalized.push(part),
            Component::CurDir => {}
            Component::ParentDir if normalized.file_name().is_some() => {
                normalized.pop();
            }
            _ => return Err(refused("produced runtime path escapes its loader base")),
        }
    }
    canonical(&normalized)?;
    Ok(normalized)
}

#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
fn capture(
    output: &Path,
    sdk: &HeldProgram,
    program: &Path,
    expected: &[u8; 32],
    runtime_roots: &[PathBuf],
    deadline: Instant,
) -> io::Result<HeldProgram> {
    canonical(program)?;
    if !program.starts_with(output)
        || output.starts_with(sdk.root())
        || sdk.root().starts_with(output)
    {
        return Err(refused("produced program and original SDK/output roots are not disjoint"));
    }
    let parent = program.parent().ok_or_else(|| refused("produced program parent missing"))?;
    let mut loader_paths = vec![parent.to_owned()];
    if runtime_roots.len() > MAX_DIRECTORIES {
        return Err(refused("produced runtime root population exceeds bound"));
    }
    for path in runtime_roots {
        canonical(path)?;
        if !path.starts_with(output) || loader_paths.contains(path) {
            return Err(refused("produced runtime root is outside original outputs or duplicated"));
        }
        loader_paths.push(path.clone());
    }
    let mut directories = BTreeMap::new();
    for path in &loader_paths {
        hold_directory(&mut directories, path, output, deadline)?;
    }
    for path in [sdk.root().join("lib"), sdk.root().join("lib/rustlib/aarch64-apple-darwin/lib")] {
        match hold_directory(&mut directories, &path, output, deadline) {
            Ok(()) => loader_paths.push(path),
            Err(error) if error.kind() == io::ErrorKind::NotFound => {}
            Err(error) => return Err(error),
        }
    }
    if loader_paths.iter().any(|path| path.as_os_str().as_bytes().contains(&b':')) {
        return Err(refused("produced runtime root contains a loader separator"));
    }
    let (executable, header) = file(&mut directories, program, true, output, deadline)?;
    if executable.before.nlink() != 1 || executable.observation.sha256 != hex(expected) {
        return Err(refused("produced executable is aliased or differs from its original digest"));
    }
    let mut pending = vec![(program.to_owned(), macho::produced_commands(&header, true)?)];
    let mut runtime = Vec::new();
    let mut seen = BTreeSet::new();
    let mut system = BTreeSet::new();
    let mut total = executable.before.len();
    let mut edges = 0usize;
    while let Some((binary, commands)) = pending.pop() {
        time(deadline)?;
        for rpath in commands.rpaths {
            if !loader_paths.contains(&expand(&rpath, &binary, program)?) {
                return Err(refused(
                    "produced image search path is outside its bound runtime roots",
                ));
            }
        }
        for load in commands.loads {
            edges =
                edges.checked_add(1).ok_or_else(|| refused("produced runtime edge overflow"))?;
            if edges > MAX_COMMANDS {
                return Err(refused("produced runtime edge population exceeds bound"));
            }
            let system_load = macho::system(&load);
            let direct = if !system_load && !load.starts_with("@rpath/") {
                let path = expand(&load, &binary, program)?;
                if !loader_paths.iter().any(|base| path.parent() == Some(base.as_path())) {
                    return Err(refused("produced dependency escapes its original runtime roots"));
                }
                Some(path)
            } else {
                None
            };
            let leaf = if let Some(leaf) = load.strip_prefix("@rpath/") {
                if leaf.is_empty() || leaf.contains('/') || matches!(leaf, "." | "..") {
                    return Err(refused("produced @rpath dependency is not a plain leaf"));
                }
                OsStr::new(leaf)
            } else {
                direct
                    .as_deref()
                    .unwrap_or_else(|| Path::new(&load))
                    .file_name()
                    .ok_or_else(|| refused("produced dependency has no library leaf"))?
            };
            // DYLD_LIBRARY_PATH searches by leaf before the original install
            // name, including absolute and loader-relative names. Bind every
            // possible override; a direct dependency must keep its exact path.
            let candidates = loader_paths.iter().map(|base| base.join(leaf));
            let mut selected = None;
            for path in candidates {
                match file(&mut directories, &path, false, output, deadline) {
                    Ok(value) => {
                        if direct.as_ref().is_some_and(|original| original != &path) {
                            return Err(refused(
                                "produced direct dependency has a loader-path override",
                            ));
                        }
                        if system_load || selected.is_some() {
                            return Err(refused(
                                "produced runtime shadows an OS dependency or is ambiguous",
                            ));
                        }
                        selected = Some(value);
                    }
                    Err(error) if error.kind() == io::ErrorKind::NotFound => {}
                    Err(error) => return Err(error),
                }
            }
            if system_load {
                system.insert(load);
                continue;
            }
            let (held, header) =
                selected.ok_or_else(|| refused("produced runtime dependency is absent"))?;
            if held.before.nlink() != 1 {
                return Err(refused("produced runtime dependency has a hard-link alias"));
            }
            if !seen.insert(held.observation.path.clone()) {
                continue;
            }
            if runtime.len() >= MAX_RUNTIME {
                return Err(refused("produced runtime population exceeds bound"));
            }
            total = total
                .checked_add(held.before.len())
                .ok_or_else(|| refused("produced runtime size overflow"))?;
            if total > MAX_TOTAL {
                return Err(refused("produced runtime byte population exceeds bound"));
            }
            pending
                .push((held.observation.path.clone(), macho::produced_commands(&header, false)?));
            runtime.push(held);
        }
    }
    for (path, held) in &mut directories {
        held.selected |= path.starts_with(sdk.root());
    }
    runtime.sort_by(|left, right| left.observation.path.cmp(&right.observation.path));
    let (host, boot) = process::host_boot()?;
    let observation = ProgramObservation {
        policy: RUNTIME_POLICY,
        scope: INPUT_SCOPE,
        executable: executable.observation.clone(),
        runtime: runtime.iter().map(|held| held.observation.clone()).collect(),
        loader_paths,
        system_dependencies: system.into_iter().collect(),
        host,
        boot,
    };
    let held =
        HeldProgram { root: output.to_owned(), executable, runtime, directories, observation };
    held.validate(deadline)?;
    Ok(held)
}
