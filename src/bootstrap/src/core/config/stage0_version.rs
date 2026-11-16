// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Version compatibility observations by actual tool role. No version grants execution,
//! SDK, source, resource, ABI, or proof authority; actual command/image checks remain separate.

use build_helper::stage0_parser::Stage0;
use semver::Version;

#[derive(Clone, Copy)]
enum Role {
    Compiler,
    Planner,
}
impl Role {
    fn of(component: &str) -> Result<Self, String> {
        match component {
            "trustc" => Ok(Self::Compiler),
            "targo" => Ok(Self::Planner),
            _ => Err(format!("unsupported stage0 component {component:?}")),
        }
    }
    fn names(self) -> (&'static str, &'static str) {
        match self {
            Self::Compiler => ("trustc", "rustc"),
            Self::Planner => ("targo", "cargo"),
        }
    }
    fn floor(self, stage0: &Stage0) -> (&'static str, &str) {
        match self {
            Self::Compiler => {
                ("min_stage0_rustc_version", stage0.config.min_stage0_rustc_version.trim())
            }
            Self::Planner => {
                ("min_stage0_cargo_version", stage0.config.min_stage0_cargo_version.trim())
            }
        }
    }
}

fn bound(raw: &str, name: &str) -> Result<Version, String> {
    let version = Version::parse(raw).map_err(|why| format!("invalid {name} ({raw:?}): {why}"))?;
    if !version.pre.is_empty() || !version.build.is_empty() {
        return Err(format!("{name} must be a stable numeric version"));
    }
    Ok(version)
}

/// The production predicate consumes the real captured stdout, not a synthesized label.
/// Compiler bounds are unchanged. The independently measured planner floor preserves the
/// existing conservative ceiling, including genuine Bootstrap's CFG_RELEASE labels.
pub(super) fn validate(
    output: &str,
    component: &str,
    stage0: &Stage0,
    compat: &str,
) -> Result<(), String> {
    let role = Role::of(component)?;
    let (native, upstream) = role.names();
    // Preserve the existing CLI protocol's literal name/version separator. In particular,
    // leading whitespace, doubled spaces and a tab separator are not a valid tool claim.
    let mut words = output.lines().next().unwrap_or("").split(' ');
    let observed =
        words.next().ok_or_else(|| format!("empty stage0 {component} version output"))?;
    if observed != native && observed != upstream {
        return Err(format!("expected {native} (or upstream {upstream}), observed {observed:?}"));
    }
    let raw = words.next().ok_or_else(|| format!("stage0 {component} version is missing"))?.trim();
    let validated = Version::parse(raw)
        .map_err(|why| format!("invalid observed {component} version {raw:?}: {why}"))?;
    // Keep the prior release-line comparison for genuine -dev/-beta/-nightly labels,
    // after strict semver parsing. This does not rewrite the retained actual observation.
    let actual = if raw.contains('-') {
        Version::parse(raw.split('-').next().unwrap())
            .map_err(|why| format!("invalid reported {component} release line: {why}"))?
    } else {
        validated
    };
    let (field, raw_floor) = role.floor(stage0);
    let floor = bound(raw_floor, &format!("src/stage0 {field}"))?;
    let ceiling = bound(compat.trim(), "src/rust-compat-version")?;
    if floor > ceiling {
        return Err(format!("stage0 {component} floor {floor} exceeds ceiling {ceiling}"));
    }
    if actual < floor {
        return Err(format!(
            "stage0 {component} {actual} is older than supported {native} floor {floor} ({field} in src/stage0)"
        ));
    }
    if actual > ceiling {
        return Err(format!(
            "stage0 {component} {actual} exceeds this tree's supported reported-version ceiling {ceiling} (src/rust-compat-version)"
        ));
    }
    Ok(())
}

#[cfg(test)]
// Trust: out-of-line unit tests, as tidy's `unit_tests` check requires: the file sits
// under stage0_version/ so the module keeps its `stage0_version::tests` path.
#[path = "stage0_version/tests.rs"]
mod tests;
