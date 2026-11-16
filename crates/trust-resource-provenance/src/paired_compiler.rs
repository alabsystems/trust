//! A constructor-bound compiler ABI pairing, never machine admission.
//!
//! Bootstrap captures this data from its completed compiler step and embeds it
//! into the final Targo. Discovery compares held content without executing a
//! configured pathname. The trusted producer, not a supplied path or JSON
//! document, selects the pairing. The native program reader retains its stated
//! same-UID namespace and system-runtime assumptions. Package transformations
//! that change these inputs invalidate the pairing.

use std::io;
use std::os::unix::ffi::OsStrExt as _;
use std::path::{Component, Path};

use serde::{Deserialize, Serialize};

use crate::program::{HeldProgram, ProgramObservation};

pub const PRODUCER_INPUT: &str = "TRUST_TARGO_PAIRED_COMPILER_PROFILE";
pub const MAX_PROFILE_BYTES: usize = 64 * 1024;

#[derive(Debug, Serialize, Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
struct Content {
    sha256: String,
    bytes: u64,
}

#[derive(Debug, Serialize, Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
struct Runtime {
    relative_path: Vec<u8>,
    content: Content,
}

#[derive(Debug, Serialize, Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
struct Profile {
    version: u32,
    worker_protocol: u32,
    target: String,
    policy: String,
    scope: String,
    executable: Content,
    runtime: Vec<Runtime>,
    loader_paths: Vec<Vec<u8>>,
    system_dependencies: Vec<String>,
}

fn refused(message: &'static str) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, message)
}

fn relative(root: &Path, path: &Path) -> io::Result<Vec<u8>> {
    let path = path
        .strip_prefix(root)
        .map_err(|_| refused("paired compiler runtime escapes its producer root"))?;
    if path.as_os_str().is_empty()
        || path.as_os_str().as_bytes().len() > 4096
        || path.components().any(|part| !matches!(part, Component::Normal(_)))
    {
        return Err(refused("paired compiler runtime has an invalid relative path"));
    }
    Ok(path.as_os_str().as_bytes().to_vec())
}

impl Profile {
    fn from_observation(root: &Path, observed: &ProgramObservation) -> io::Result<Self> {
        let mut profile = Self {
            version: 1,
            worker_protocol: 2,
            target: "aarch64-apple-darwin".to_owned(),
            policy: observed.policy.to_owned(),
            scope: observed.scope.to_owned(),
            executable: Content {
                sha256: observed.executable.sha256.clone(),
                bytes: observed.executable.bytes,
            },
            runtime: observed
                .runtime
                .iter()
                .map(|file| {
                    Ok(Runtime {
                        relative_path: relative(root, &file.path)?,
                        content: Content { sha256: file.sha256.clone(), bytes: file.bytes },
                    })
                })
                .collect::<io::Result<_>>()?,
            loader_paths: observed
                .loader_paths
                .iter()
                .map(|path| relative(root, path))
                .collect::<io::Result<_>>()?,
            system_dependencies: observed.system_dependencies.clone(),
        };
        profile.runtime.sort_by(|left, right| left.relative_path.cmp(&right.relative_path));
        profile.validate()?;
        Ok(profile)
    }

    fn validate(&self) -> io::Result<()> {
        use std::ffi::OsStr;
        if self.version != 1
            || self.worker_protocol != 2
            || self.target != "aarch64-apple-darwin"
            || self.policy != crate::program::RUNTIME_POLICY
            || self.scope != crate::program::INPUT_SCOPE
            || self.runtime.len() > 128
            || self.loader_paths.len() > 256
            || self.system_dependencies.len() > 4096
        {
            return Err(refused("unsupported paired compiler profile"));
        }
        let mut bytes = 0u64;
        for content in std::iter::once(&self.executable)
            .chain(self.runtime.iter().map(|runtime| &runtime.content))
        {
            if content.bytes == 0
                || content.bytes > 1024 * 1024 * 1024
                || content.sha256.len() != 64
                || !content
                    .sha256
                    .bytes()
                    .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
            {
                return Err(refused("invalid paired compiler content identity"));
            }
            bytes = bytes
                .checked_add(content.bytes)
                .ok_or_else(|| refused("paired compiler size overflow"))?;
        }
        if bytes > 4 * 1024 * 1024 * 1024 {
            return Err(refused("paired compiler runtime exceeds its bound"));
        }
        for path in
            self.runtime.iter().map(|runtime| &runtime.relative_path).chain(&self.loader_paths)
        {
            let path = Path::new(OsStr::from_bytes(path));
            if path.as_os_str().is_empty()
                || path.as_os_str().as_bytes().len() > 4096
                || path.as_os_str().as_bytes().contains(&0)
                || path.components().any(|part| !matches!(part, Component::Normal(_)))
            {
                return Err(refused("invalid paired compiler relative path"));
            }
        }
        if self.runtime.windows(2).any(|pair| pair[0].relative_path >= pair[1].relative_path)
            || self.system_dependencies.windows(2).any(|pair| pair[0] >= pair[1])
            || self.system_dependencies.iter().any(|path| path.len() > 4096 || path.contains('\0'))
        {
            return Err(refused("noncanonical paired compiler runtime closure"));
        }
        Ok(())
    }

    fn decode(encoded: &str) -> io::Result<Self> {
        if encoded.len() > MAX_PROFILE_BYTES {
            return Err(refused("paired compiler profile exceeds its bound"));
        }
        let profile: Self = serde_json::from_str(encoded)
            .map_err(|_| refused("invalid paired compiler profile"))?;
        profile.validate()?;
        Ok(profile)
    }
}

/// Called only by the canonical SDK constructor after its known compiler's
/// exact standalone query. This data is not independently source authority.
fn require_reply(reply: &[u8]) -> io::Result<()> {
    #[derive(Deserialize)]
    #[serde(deny_unknown_fields)]
    struct Reply {
        version: u32,
        protocol: u32,
        cpu_workers: bool,
    }
    if reply.len() > 1024 {
        return Err(refused("compiler protocol reply exceeds its bound"));
    }
    let reply: Reply =
        serde_json::from_slice(reply).map_err(|_| refused("invalid compiler protocol reply"))?;
    if reply.version != 1 || reply.protocol != 2 || !reply.cpu_workers {
        return Err(refused("producer compiler does not support native workers"));
    }
    Ok(())
}

pub fn capture(
    held: &HeldProgram,
    reply: &[u8],
    deadline: std::time::Instant,
) -> io::Result<String> {
    require_reply(reply)?;
    held.validate(deadline)?;
    let profile = Profile::from_observation(held.root(), held.observation())?;
    let encoded = serde_json::to_string(&profile).map_err(io::Error::other)?;
    if encoded.len() > MAX_PROFILE_BYTES {
        return Err(refused("paired compiler profile exceeds its bound"));
    }
    Ok(encoded)
}

/// Match the producer's compiled profile without executing any selected tool.
/// The returned original inputs must remain held through actual execution.
pub fn hold(
    root: &Path,
    compiler: &Path,
    encoded: &str,
    deadline: std::time::Instant,
) -> io::Result<HeldProgram> {
    let expected = Profile::decode(encoded)?;
    let mut digest = [0; 32];
    for (output, pair) in
        digest.iter_mut().zip(expected.executable.sha256.as_bytes().chunks_exact(2))
    {
        let digit = |byte: u8| {
            if byte <= b'9' { byte - b'0' } else { byte - b'a' + 10 }
        };
        *output = digit(pair[0]) * 16 + digit(pair[1]);
    }
    let held = HeldProgram::open(root, compiler, &digest, deadline)?;
    if Profile::from_observation(root, held.observation())? != expected {
        return Err(refused(
            "configured compiler/runtime differs from the producer's paired cohort",
        ));
    }
    Ok(held)
}

#[cfg(test)]
#[path = "paired_compiler/tests.rs"]
mod tests;
