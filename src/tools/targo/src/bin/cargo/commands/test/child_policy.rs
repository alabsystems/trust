//! The native test owner's bounded, non-authority narrowing request.

use std::num::NonZeroU64;
use std::time::Duration;

#[derive(serde::Deserialize)]
#[serde(deny_unknown_fields)]
struct Request {
    version: u8,
    inactivity_ms: NonZeroU64,
    resident_bytes: Option<NonZeroU64>,
}

pub(super) fn parse(value: &str) -> Result<cargo_util::ChildSupervision, String> {
    if value.len() > 256 {
        return Err("ordinary child policy exceeds its bounded request size".into());
    }
    let request: Request = serde_json::from_str(value)
        .map_err(|error| format!("invalid ordinary child policy: {error}"))?;
    if request.version != 1 {
        return Err("unsupported ordinary child policy version".into());
    }
    cargo_util::ChildSupervision::new(
        Duration::from_millis(request.inactivity_ms.get()),
        request.resident_bytes,
    )
    .map_err(|error| error.to_string())
}

#[cfg(test)]
#[path = "child_policy/tests.rs"]
mod tests;
