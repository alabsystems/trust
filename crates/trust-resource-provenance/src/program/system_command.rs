//! Original native command inputs for an ordinary held child. This profile is
//! deliberately independent of SDK selection and completed-runtime authority.

use super::*;

/// A live original executable whose load commands name only system libraries.
/// There is no saved-record constructor and no conversion to an SDK owner.
pub struct HeldSystemCommand {
    original: HeldProgram,
}

enum SystemImports {
    NoSearchPaths,
    AbsoluteOnly,
}

impl HeldSystemCommand {
    pub fn open(program: &Path, deadline: Instant) -> io::Result<Self> {
        Self::capture(program, deadline, SystemImports::NoSearchPaths)
    }

    /// Retain an independent native helper whose every static import names an
    /// absolute system library. Unused LC_RPATH entries add no loader roots.
    /// This is a distinct input profile, not the strict v1 command constructor,
    /// an SDK owner, or evidence of functional compatibility.
    pub fn open_absolute_system_imports(program: &Path, deadline: Instant) -> io::Result<Self> {
        Self::capture(program, deadline, SystemImports::AbsoluteOnly)
    }

    fn capture(program: &Path, deadline: Instant, imports: SystemImports) -> io::Result<Self> {
        #[cfg(not(all(target_os = "macos", target_arch = "aarch64")))]
        {
            let _ = (program, deadline, imports);
            Err(io::Error::new(
                io::ErrorKind::Unsupported,
                "native system command profile is unavailable",
            ))
        }
        #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
        {
            canonical(program)?;
            let root = program.parent().ok_or_else(|| refused("native command has no parent"))?;
            let mut directories = BTreeMap::new();
            let (executable, header) = file(&mut directories, program, true, root, deadline)?;
            let commands = macho::commands(&header, true)?;
            if (matches!(imports, SystemImports::NoSearchPaths) && !commands.rpaths.is_empty())
                || commands.loads.iter().any(|load| !macho::system(load))
            {
                return Err(refused("native command requires a non-system runtime search"));
            }
            let (host, boot) = process::host_boot()?;
            let observation = ProgramObservation {
                policy: match imports {
                    SystemImports::NoSearchPaths => "native-command/macho-arm64-system-only-v1",
                    SystemImports::AbsoluteOnly => {
                        "native-command/macho-arm64-absolute-system-imports-v1"
                    }
                },
                scope: INPUT_SCOPE,
                executable: executable.observation.clone(),
                runtime: Vec::new(),
                loader_paths: Vec::new(),
                system_dependencies: commands
                    .loads
                    .into_iter()
                    .collect::<BTreeSet<_>>()
                    .into_iter()
                    .collect(),
                host,
                boot,
            };
            let original = HeldProgram {
                root: root.to_owned(),
                executable,
                runtime: Vec::new(),
                directories,
                observation,
            };
            original.validate(deadline)?;
            Ok(Self { original })
        }
    }

    pub fn program(&self) -> &Path {
        self.original.program()
    }
    pub fn observation(&self) -> &ProgramObservation {
        self.original.observation()
    }
    pub fn validate(&self, deadline: Instant) -> io::Result<()> {
        self.original.validate(deadline)
    }

    /// Require the distinct Bootstrap fixed-startup support declaration from
    /// this original held image. It is no CPU/SDK/runtime-completion grant.
    pub fn require_bootstrap_fixed_protocol(
        &self,
        _expected: &[u8; 64],
        deadline: Instant,
    ) -> io::Result<()> {
        self.validate(deadline)?;
        #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
        protocol_marker::require(
            &self.original.executable.file,
            protocol_marker::Profile::BootstrapFixed,
            _expected,
            deadline,
        )?;
        #[cfg(not(all(target_os = "macos", target_arch = "aarch64")))]
        return Err(io::Error::new(
            io::ErrorKind::Unsupported,
            "native Bootstrap declaration profile is unavailable",
        ));
        #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
        self.validate(deadline)
    }

    /// Observe the actual original child image. An already running ordinary
    /// child is not a suspended-GO boundary or completed-runtime authority.
    pub fn validate_loaded(&self, child: process::Identity, deadline: Instant) -> io::Result<()> {
        self.original.validate_loaded(child, deadline)
    }
}

#[cfg(all(test, target_os = "macos", target_arch = "aarch64"))]
mod tests;
