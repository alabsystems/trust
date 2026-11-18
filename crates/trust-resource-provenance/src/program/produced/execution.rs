// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates

//! Exact startup environment over the SAME retained produced inputs. An
//! optional fallback is preserved only when it cannot resolve a startup edge;
//! it supplies no runtime root or authority for later arbitrary dynamic loads.

use super::*;

pub struct HeldProducedExecution {
    image: Arc<HeldProducedProgram>,
    environment: BTreeMap<OsString, OsString>,
    fallback: bool,
}

impl HeldProducedProgram {
    /// Bind exact loader expectations after compiler writers have retired.
    /// Canonical held library roots remain mandatory. A fallback value is
    /// inert only if every system import exists in the active OS shared cache
    /// and every non-system edge already resolves inside these held inputs.
    /// This neither attests the OS nor authorizes later arbitrary dlopen calls.
    pub fn execution(
        self: &Arc<Self>,
        environment: &[(OsString, OsString)],
        deadline: Instant,
    ) -> io::Result<HeldProducedExecution> {
        self.validate(deadline)?;
        let mut expected = BTreeMap::new();
        let mut bytes = 0usize;
        for (name, value) in environment {
            bytes = bytes
                .checked_add(name.as_bytes().len())
                .and_then(|bytes| bytes.checked_add(value.as_bytes().len()))
                .ok_or_else(|| refused("produced loader environment size overflow"))?;
            if bytes > 1024 * 1024 || expected.insert(name.clone(), value.clone()).is_some() {
                return Err(refused("produced loader expectations exceed bounds or repeat a key"));
            }
        }
        let fallback = expected.remove(OsStr::new("DYLD_FALLBACK_LIBRARY_PATH"));
        let canonical: BTreeMap<_, _> = self.runtime_environment()?.into_iter().collect();
        if expected != canonical {
            return Err(refused("produced loader expectations differ from original runtime roots"));
        }
        if let Some(value) = fallback {
            expected.insert(OsString::from("DYLD_FALLBACK_LIBRARY_PATH"), value);
        }
        let selected = HeldProducedExecution {
            image: Arc::clone(self),
            fallback: expected.contains_key(OsStr::new("DYLD_FALLBACK_LIBRARY_PATH")),
            environment: expected,
        };
        selected.validate(deadline)?;
        Ok(selected)
    }
}

impl HeldProducedExecution {
    pub fn program(&self) -> &Path {
        self.image.program()
    }
    pub fn environment(&self) -> &BTreeMap<OsString, OsString> {
        &self.environment
    }
    pub fn validate(&self, deadline: Instant) -> io::Result<()> {
        self.image.validate(deadline)?;
        if self.fallback {
            for path in &self.image.observation().system_dependencies {
                time(deadline)?;
                require_system_cache_path(path)?;
            }
        }
        self.image.validate(deadline)
    }
    pub fn validate_loaded(&self, child: process::Identity, deadline: Instant) -> io::Result<()> {
        self.validate(deadline)?;
        self.image.validate_loaded(child, deadline)?;
        self.validate(deadline)
    }
}

fn require_system_cache_path(path: &str) -> io::Result<()> {
    #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
    {
        unsafe extern "C" {
            fn _dyld_shared_cache_contains_path(path: *const std::ffi::c_char) -> bool;
        }
        let name = CString::new(path).map_err(|_| refused("system import contains NUL"))?;
        // SAFETY: the OS query borrows this terminated string for the call and
        // returns membership in the active cache; it does not load the image.
        if !unsafe { _dyld_shared_cache_contains_path(name.as_ptr()) } {
            return Err(refused(
                "fallback could resolve a system import absent from the active cache",
            ));
        }
        Ok(())
    }
    #[cfg(not(all(target_os = "macos", target_arch = "aarch64")))]
    {
        let _ = path;
        Err(io::Error::new(io::ErrorKind::Unsupported, "native system cache query unavailable"))
    }
}

#[cfg(all(test, target_os = "macos", target_arch = "aarch64"))]
mod tests {
    use super::*;
    #[test]
    fn fallback_requires_actual_active_system_image_instead_of_system_path_spelling() {
        require_system_cache_path("/usr/lib/libSystem.B.dylib").unwrap();
        assert!(
            require_system_cache_path("/usr/lib/trust-missing-native-runtime-image.dylib").is_err()
        );
    }
}
