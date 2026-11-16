//! Stable frontend potential for a seed Cargo route that has no Targo planner.
use std::ffi::{OsStr, OsString};

/// Bootstrap-internal potential, not a grant or a worker count. The concrete
/// shim still requires an unverified Trust seed and a validated GNU scheduler.
pub const BOOTSTRAP_FRONTEND_CEILING_ENV: &str = "RUSTC_BOOTSTRAP_FRONTEND_CEILING";

/// Explicit bootstrap configuration owns its existing argv. Otherwise capture
/// the local affinity/quota ceiling once, independently of admission/load/jobs.
pub fn bootstrap_seed_frontend_ceiling(
    configured: Option<u32>,
    local: Option<usize>,
) -> Option<u32> {
    if configured.is_some() {
        return None;
    }
    local.and_then(|value| u32::try_from(value).ok()).filter(|value| *value != 0)
}

/// Select potential only after the shim resolves a real unverified seed
/// compile and validates the inherited scheduler. This never creates credits:
/// each additional frontend worker still needs that GNU scheduler's token.
pub fn bootstrap_seed_frontend_threads(
    args: &[OsString],
    unverified_seed_compile: bool,
    inherited_scheduler: bool,
    ceiling: Option<&OsStr>,
) -> Result<Option<u32>, &'static str> {
    if !unverified_seed_compile || !inherited_scheduler || explicit_threads(args) {
        return Ok(None);
    }
    let Some(ceiling) = ceiling else { return Ok(None) };
    let value = ceiling.to_str().ok_or("bootstrap frontend ceiling is not UTF-8")?;
    if value.is_empty() || !value.bytes().all(|byte| byte.is_ascii_digit()) {
        return Err("bootstrap frontend ceiling must be a positive u32");
    }
    let value = value
        .parse::<u32>()
        .ok()
        .filter(|value| *value != 0)
        .ok_or("bootstrap frontend ceiling must be a positive u32")?;
    Ok(Some(value))
}

fn explicit_threads(args: &[OsString]) -> bool {
    args.iter().enumerate().any(|(index, arg)| {
        let Some(arg) = arg.to_str() else { return false };
        let option = if arg == "-Z" {
            args.get(index + 1).and_then(|next| next.to_str())
        } else {
            arg.strip_prefix("-Z")
        };
        option.is_some_and(|option| option.split('=').next() == Some("threads"))
    })
}

// Trust: out-of-line unit tests, as tidy's `unit_tests` check requires.
#[cfg(test)]
mod tests;
