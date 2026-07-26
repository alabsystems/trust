// Linked Trust toolchain surface detection: classify the cargo surface (targo, trustfmt, etc.)
// next to a discovered trustc and decide whether it is publication-grade.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::env;
use std::path::{Path, PathBuf};

use serde::Serialize;

use super::discovery::{
    canonicalize_or_self, current_exe_sibling_rustc, host_executable_name, is_trustc_path,
    path_is_executable_file, path_is_executable_target, same_file_or_exact_contents,
};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case")]
pub(crate) enum LinkedTrustToolchainStatusKind {
    Visible,
    Missing,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub(crate) struct LinkedTrustToolchainStatus {
    pub(crate) status: LinkedTrustToolchainStatusKind,
    pub(crate) rustc: Option<PathBuf>,
    pub(crate) detail: Option<String>,
}

impl LinkedTrustToolchainStatus {
    pub(crate) fn is_visible(&self) -> bool {
        matches!(self.status, LinkedTrustToolchainStatusKind::Visible)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub(crate) struct LinkedTrustCargoSurfaceStatus {
    pub(crate) kind: LinkedTrustCargoSurfaceKind,
    pub(crate) ready: bool,
    pub(crate) same_sysroot: bool,
    pub(crate) sysroot: Option<PathBuf>,
    pub(crate) bin_dir: Option<PathBuf>,
    pub(crate) targo: Option<PathBuf>,
    pub(crate) targo_trust: Option<PathBuf>,
    pub(crate) required_tools: Vec<LinkedTrustSurfaceToolStatus>,
    pub(crate) optional_tools: Vec<LinkedTrustSurfaceToolStatus>,
    pub(crate) detail: Option<String>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case")]
pub(crate) enum LinkedTrustSurfaceToolStatusKind {
    Present,
    Missing,
    OptionalMissing,
    AmbientFallback,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub(crate) struct LinkedTrustSurfaceToolStatus {
    pub(crate) name: String,
    pub(crate) required: bool,
    pub(crate) status: LinkedTrustSurfaceToolStatusKind,
    pub(crate) path: Option<PathBuf>,
    pub(crate) sysroot: Option<PathBuf>,
    pub(crate) bin_dir: Option<PathBuf>,
    pub(crate) detail: Option<String>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case")]
pub(crate) enum LinkedTrustCargoSurfaceKind {
    InstalledReady,
    Stage2Ready,
    Stage1CompilerOnly,
    AmbientFallback,
    Missing,
    InvalidInheritedNameEvidence,
}

impl LinkedTrustCargoSurfaceKind {
    pub(crate) fn label(self) -> &'static str {
        match self {
            Self::InstalledReady => "installed-ready",
            Self::Stage2Ready => "stage2-ready",
            Self::Stage1CompilerOnly => "stage1-compiler-only",
            Self::AmbientFallback => "ambient-fallback",
            Self::Missing => "missing",
            Self::InvalidInheritedNameEvidence => "invalid-inherited-name-evidence",
        }
    }
}

pub(crate) fn detect_linked_trust_toolchain() -> LinkedTrustToolchainStatus {
    if let Some(rustc) = current_exe_sibling_rustc() {
        return LinkedTrustToolchainStatus {
            status: LinkedTrustToolchainStatusKind::Visible,
            rustc: Some(rustc),
            detail: None,
        };
    }

    LinkedTrustToolchainStatus {
        status: LinkedTrustToolchainStatusKind::Missing,
        rustc: None,
        detail: Some("Trust product discovery uses only Trust roots".to_string()),
    }
}

fn empty_linked_cargo_surface(
    kind: LinkedTrustCargoSurfaceKind,
    detail: String,
) -> LinkedTrustCargoSurfaceStatus {
    let (required_tools, optional_tools) = unresolved_surface_tools(&detail);
    LinkedTrustCargoSurfaceStatus {
        kind,
        ready: false,
        same_sysroot: false,
        sysroot: None,
        bin_dir: None,
        targo: None,
        targo_trust: None,
        required_tools,
        optional_tools,
        detail: Some(detail),
    }
}

fn detect_linked_trust_cargo_surface_with(
    linked_toolchain: &LinkedTrustToolchainStatus,
) -> LinkedTrustCargoSurfaceStatus {
    let ambient_search_paths = env::var_os("PATH")
        .map(|path| env::split_paths(&path).collect::<Vec<_>>())
        .unwrap_or_default();
    detect_linked_trust_cargo_surface_with_search(linked_toolchain, &ambient_search_paths)
}

pub(super) fn detect_linked_trust_cargo_surface_with_search(
    linked_toolchain: &LinkedTrustToolchainStatus,
    ambient_search_paths: &[PathBuf],
) -> LinkedTrustCargoSurfaceStatus {
    let Some(linked_compiler) = linked_toolchain.rustc.as_deref() else {
        return empty_linked_cargo_surface(
            LinkedTrustCargoSurfaceKind::Missing,
            linked_toolchain
                .detail
                .clone()
                .unwrap_or_else(|| "Trust-local cargo surface is not visible".to_string()),
        );
    };
    if !linked_toolchain.is_visible() {
        return empty_linked_cargo_surface(
            LinkedTrustCargoSurfaceKind::Missing,
            linked_toolchain
                .detail
                .clone()
                .unwrap_or_else(|| "Trust-local cargo surface is not visible".to_string()),
        );
    }

    let Some(bin_dir) = linked_compiler.parent() else {
        return empty_linked_cargo_surface(
            LinkedTrustCargoSurfaceKind::Missing,
            format!(
                "linked Trust compiler path has no parent directory: {}",
                linked_compiler.display()
            ),
        );
    };
    let bin_dir = canonicalize_or_self(bin_dir.to_path_buf());
    let selected_sysroot = trust_sysroot_for_bin_dir(&bin_dir);
    if !is_trustc_path(linked_compiler) {
        let linked_name = linked_compiler.file_name();
        let rustc_alias_name = host_executable_name("rustc");
        let sibling_trustc = bin_dir.join(host_executable_name("trustc"));
        if linked_name.is_some_and(|name| name == rustc_alias_name.as_str())
            && path_is_executable_file(&sibling_trustc)
            && path_is_executable_target(linked_compiler)
            && same_file_or_exact_contents(linked_compiler, &sibling_trustc)
        {
            // Same-sysroot `rustc` is compatibility surface. The canonical sibling
            // still has to exist and the regular surface checks below enforce the
            // rest of the Trust-preferred tools and aliases.
        } else {
            let (required_tools, optional_tools, _) =
                classify_trust_surface_tools(&bin_dir, ambient_search_paths);
            return LinkedTrustCargoSurfaceStatus {
                kind: LinkedTrustCargoSurfaceKind::InvalidInheritedNameEvidence,
                ready: false,
                same_sysroot: false,
                sysroot: selected_sysroot,
                bin_dir: Some(bin_dir),
                targo: tool_path(&required_tools, "targo"),
                targo_trust: tool_path(&required_tools, "targo-trust"),
                required_tools,
                optional_tools,
                detail: Some(format!(
                    "selected compiler `{}` is not canonical `trustc` and is not a same-sysroot `rustc` alias with sibling `trustc`",
                    linked_compiler.display()
                )),
            };
        }
    }

    let stage = trust_root_stage(&bin_dir);
    if stage == Some("stage1") {
        let (required_tools, optional_tools, _) =
            classify_trust_surface_tools(&bin_dir, ambient_search_paths);
        return LinkedTrustCargoSurfaceStatus {
            kind: LinkedTrustCargoSurfaceKind::Stage1CompilerOnly,
            ready: false,
            same_sysroot: false,
            sysroot: selected_sysroot,
            bin_dir: Some(bin_dir),
            targo: tool_path(&required_tools, "targo"),
            targo_trust: tool_path(&required_tools, "targo-trust"),
            required_tools,
            optional_tools,
            detail: Some(format!(
                "linked Trust compiler is under stage1 at {}; stage1 is compiler-only evidence and is not accepted for daily-driver readiness",
                linked_compiler.display()
            )),
        };
    }

    let (required_tools, optional_tools, blocker) =
        classify_trust_surface_tools(&bin_dir, ambient_search_paths);
    let targo = tool_path(&required_tools, "targo");
    let targo_trust = tool_path(&required_tools, "targo-trust");

    if let Some((kind, detail)) = blocker {
        return LinkedTrustCargoSurfaceStatus {
            kind,
            ready: false,
            same_sysroot: false,
            sysroot: selected_sysroot,
            bin_dir: Some(bin_dir),
            targo,
            targo_trust,
            required_tools,
            optional_tools,
            detail: Some(detail),
        };
    }

    let kind = if matches!(stage, Some("stage2" | "stage3")) {
        LinkedTrustCargoSurfaceKind::Stage2Ready
    } else {
        LinkedTrustCargoSurfaceKind::InstalledReady
    };

    LinkedTrustCargoSurfaceStatus {
        kind,
        ready: true,
        same_sysroot: true,
        sysroot: selected_sysroot,
        bin_dir: Some(bin_dir),
        targo,
        targo_trust,
        required_tools,
        optional_tools,
        detail: None,
    }
}

pub(crate) fn detect_linked_trust_cargo_surface(
    linked_toolchain: &LinkedTrustToolchainStatus,
) -> LinkedTrustCargoSurfaceStatus {
    detect_linked_trust_cargo_surface_with(linked_toolchain)
}

fn trust_root_stage(bin_dir: &Path) -> Option<&'static str> {
    match bin_dir.parent()?.file_name()?.to_str()? {
        "stage1" => Some("stage1"),
        "stage2" => Some("stage2"),
        "stage3" => Some("stage3"),
        _ => None,
    }
}

fn trust_sysroot_for_bin_dir(bin_dir: &Path) -> Option<PathBuf> {
    bin_dir.parent().map(|sysroot| canonicalize_or_self(sysroot.to_path_buf()))
}

fn ambient_tool_fallback(
    tool: &str,
    selected_bin_dir: &Path,
    ambient_search_paths: &[PathBuf],
) -> Option<PathBuf> {
    ambient_search_paths.iter().find_map(|dir| {
        let candidate = dir.join(host_executable_name(tool));
        if !path_is_executable_file(&candidate) {
            return None;
        }
        let candidate = canonicalize_or_self(candidate);
        (candidate.parent().map(|parent| canonicalize_or_self(parent.to_path_buf()))
            != Some(selected_bin_dir.to_path_buf()))
        .then_some(candidate)
    })
}

#[derive(Debug, Clone, Copy)]
pub(super) struct LinkedTrustSurfaceToolSpec {
    pub(super) name: &'static str,
    pub(super) required: bool,
    pub(super) required_compatibility_aliases: &'static [&'static str],
}

pub(super) const LINKED_TRUST_SURFACE_TOOLS: &[LinkedTrustSurfaceToolSpec] = &[
    LinkedTrustSurfaceToolSpec {
        name: "trustc",
        required: true,
        required_compatibility_aliases: &["rustc"],
    },
    LinkedTrustSurfaceToolSpec {
        name: "targo",
        required: true,
        required_compatibility_aliases: &["cargo"],
    },
    LinkedTrustSurfaceToolSpec {
        name: "targo-trust",
        required: true,
        required_compatibility_aliases: &[],
    },
    LinkedTrustSurfaceToolSpec {
        name: "trustd",
        required: true,
        required_compatibility_aliases: &[],
    },
    LinkedTrustSurfaceToolSpec {
        name: "trustdoc",
        required: true,
        required_compatibility_aliases: &[],
    },
    LinkedTrustSurfaceToolSpec {
        name: "trustfmt",
        required: true,
        required_compatibility_aliases: &[],
    },
    LinkedTrustSurfaceToolSpec {
        name: "targo-fmt",
        required: true,
        required_compatibility_aliases: &[],
    },
    LinkedTrustSurfaceToolSpec {
        name: "tippy",
        required: true,
        required_compatibility_aliases: &[],
    },
    LinkedTrustSurfaceToolSpec {
        name: "targo-tippy",
        required: true,
        required_compatibility_aliases: &[],
    },
    LinkedTrustSurfaceToolSpec {
        name: "tippy-driver",
        required: true,
        required_compatibility_aliases: &[],
    },
    LinkedTrustSurfaceToolSpec {
        name: "trust-analyzer",
        required: true,
        required_compatibility_aliases: &[],
    },
    LinkedTrustSurfaceToolSpec {
        name: "trust-miri",
        required: false,
        required_compatibility_aliases: &[],
    },
    LinkedTrustSurfaceToolSpec {
        name: "targo-miri",
        required: false,
        required_compatibility_aliases: &[],
    },
];

// Public secondary names are intentionally Trust-only. These leaves are
// admitted solely as legacy stage0 archive inputs and must be translated away
// before a selected sysroot can count as linked Trust release evidence.
pub(crate) const FORBIDDEN_TRUST_PUBLIC_BIN_NAMES: &[&str] = &[
    "cargo-trust",
    "tcargo",
    "tcargo-trust",
    "tcargo-fmt",
    "rustdoc",
    "rustfmt",
    "cargo-fmt",
    "cargo-clippy",
    "clippy-driver",
    "targo-clippy",
    "trust-clippy",
    "trust-clippy-driver",
    "rust-analyzer",
    "miri",
    "cargo-miri",
    "rust-gdb",
    "rust-gdbgui",
    "rust-lldb",
    "rust-windbg.cmd",
];

pub(crate) const FORBIDDEN_TRUST_PUBLIC_LIBEXEC_NAMES: &[&str] = &["rust-analyzer-proc-macro-srv"];

fn public_bin_path(bin_dir: &Path, name: &str) -> PathBuf {
    // Windows debugger launchers are command scripts rather than PE
    // executables, so they do not take EXE_SUFFIX.
    if name.ends_with(".cmd") {
        bin_dir.join(name)
    } else {
        bin_dir.join(host_executable_name(name))
    }
}

fn path_entry_exists(path: &Path) -> bool {
    std::fs::symlink_metadata(path).is_ok()
}

pub(crate) fn forbidden_trust_surface_entries(bin_dir: &Path) -> Vec<PathBuf> {
    let mut entries = FORBIDDEN_TRUST_PUBLIC_BIN_NAMES
        .iter()
        .map(|name| public_bin_path(bin_dir, name))
        .filter(|path| path_entry_exists(path))
        .collect::<Vec<_>>();
    if let Some(sysroot) = bin_dir.parent() {
        let libexec = sysroot.join("libexec");
        entries.extend(
            FORBIDDEN_TRUST_PUBLIC_LIBEXEC_NAMES
                .iter()
                .map(|name| libexec.join(host_executable_name(name)))
                .filter(|path| path_entry_exists(path)),
        );
    }
    entries
}

fn unresolved_surface_tools(
    detail: &str,
) -> (Vec<LinkedTrustSurfaceToolStatus>, Vec<LinkedTrustSurfaceToolStatus>) {
    let mut required = Vec::new();
    let mut optional = Vec::new();
    for spec in LINKED_TRUST_SURFACE_TOOLS {
        let status = LinkedTrustSurfaceToolStatus {
            name: spec.name.to_string(),
            required: spec.required,
            status: if spec.required {
                LinkedTrustSurfaceToolStatusKind::Missing
            } else {
                LinkedTrustSurfaceToolStatusKind::OptionalMissing
            },
            path: None,
            sysroot: None,
            bin_dir: None,
            detail: Some(detail.to_string()),
        };
        if spec.required {
            required.push(status);
        } else {
            optional.push(status);
        }
    }
    (required, optional)
}

fn classify_trust_surface_tools(
    bin_dir: &Path,
    ambient_search_paths: &[PathBuf],
) -> (
    Vec<LinkedTrustSurfaceToolStatus>,
    Vec<LinkedTrustSurfaceToolStatus>,
    Option<(LinkedTrustCargoSurfaceKind, String)>,
) {
    let mut required = Vec::new();
    let mut optional = Vec::new();
    let mut blocker = None;

    for spec in LINKED_TRUST_SURFACE_TOOLS {
        let status = classify_trust_surface_tool(*spec, bin_dir, ambient_search_paths);
        if blocker.is_none() {
            blocker = blocker_for_surface_tool(&status);
        }
        if spec.required {
            required.push(status);
        } else {
            optional.push(status);
        }
    }

    if blocker.is_none() {
        if let Some(path) = forbidden_trust_surface_entries(bin_dir).into_iter().next() {
            blocker = Some((
                LinkedTrustCargoSurfaceKind::InvalidInheritedNameEvidence,
                format!(
                    "selected Trust root contains forbidden retired public entrypoint at {}",
                    path.display()
                ),
            ));
        }
    }

    (required, optional, blocker)
}

fn classify_trust_surface_tool(
    spec: LinkedTrustSurfaceToolSpec,
    bin_dir: &Path,
    ambient_search_paths: &[PathBuf],
) -> LinkedTrustSurfaceToolStatus {
    let expected = bin_dir.join(host_executable_name(spec.name));
    let expected_sysroot = trust_sysroot_for_bin_dir(bin_dir);
    if !path_is_executable_file(&expected) {
        if let Some(ambient) = ambient_tool_fallback(spec.name, bin_dir, ambient_search_paths) {
            let detail = format!(
                "canonical `{}` is missing from selected Trust root {}, but an ambient `{}` exists at {}; ambient fallback is not Trust release evidence",
                spec.name,
                bin_dir.display(),
                spec.name,
                ambient.display()
            );
            return LinkedTrustSurfaceToolStatus {
                name: spec.name.to_string(),
                required: spec.required,
                status: if spec.required {
                    LinkedTrustSurfaceToolStatusKind::AmbientFallback
                } else {
                    LinkedTrustSurfaceToolStatusKind::OptionalMissing
                },
                path: if spec.required { Some(ambient) } else { None },
                sysroot: None,
                bin_dir: None,
                detail: Some(detail),
            };
        }

        return LinkedTrustSurfaceToolStatus {
            name: spec.name.to_string(),
            required: spec.required,
            status: if spec.required {
                LinkedTrustSurfaceToolStatusKind::Missing
            } else {
                LinkedTrustSurfaceToolStatusKind::OptionalMissing
            },
            path: None,
            sysroot: None,
            bin_dir: None,
            detail: Some(format!(
                "Trust toolchain is missing canonical `{}` at {}",
                spec.name,
                expected.display()
            )),
        };
    }

    let path = canonicalize_or_self(expected.clone());
    if path.parent().map(|parent| canonicalize_or_self(parent.to_path_buf()))
        != Some(bin_dir.to_path_buf())
    {
        return LinkedTrustSurfaceToolStatus {
            name: spec.name.to_string(),
            required: spec.required,
            status: LinkedTrustSurfaceToolStatusKind::AmbientFallback,
            path: Some(path.clone()),
            sysroot: path.parent().and_then(trust_sysroot_for_bin_dir),
            bin_dir: path.parent().map(|parent| canonicalize_or_self(parent.to_path_buf())),
            detail: Some(format!(
                "linked `{}` resolves outside the selected Trust toolchain: expected {}, got {}; this may be an ambient fallback or a stale `trust` alias",
                spec.name,
                expected.display(),
                path.display()
            )),
        };
    }

    let mut missing_aliases = Vec::new();
    let mut invalid_alias_bindings = Vec::new();
    for name in spec.required_compatibility_aliases {
        let alias_path = bin_dir.join(host_executable_name(name));
        if !path_is_executable_target(&alias_path) {
            missing_aliases.push(*name);
            continue;
        }
        match std::fs::canonicalize(&alias_path) {
            Ok(resolved)
                if resolved.parent().map(|parent| canonicalize_or_self(parent.to_path_buf()))
                    == Some(bin_dir.to_path_buf())
                    && same_file_or_exact_contents(&alias_path, &expected) => {}
            Ok(resolved)
                if resolved.parent().map(|parent| canonicalize_or_self(parent.to_path_buf()))
                    == Some(bin_dir.to_path_buf()) =>
            {
                invalid_alias_bindings.push(format!(
                    "{name} does not bind to canonical {} at {}",
                    spec.name,
                    expected.display()
                ));
            }
            Ok(resolved) => invalid_alias_bindings.push(format!(
                "{name} resolves outside the selected Trust bin directory to {}",
                resolved.display()
            )),
            Err(error) => invalid_alias_bindings.push(format!(
                "{name} could not be canonicalized at {}: {error}",
                alias_path.display()
            )),
        }
    }
    if !missing_aliases.is_empty() {
        return LinkedTrustSurfaceToolStatus {
            name: spec.name.to_string(),
            required: spec.required,
            status: LinkedTrustSurfaceToolStatusKind::Missing,
            path: Some(path),
            sysroot: expected_sysroot,
            bin_dir: Some(bin_dir.to_path_buf()),
            detail: Some(format!(
                "Trust toolchain has canonical `{}` but is missing required same-sysroot compatibility alias(es): {}",
                spec.name,
                missing_aliases.join(", ")
            )),
        };
    }
    if !invalid_alias_bindings.is_empty() {
        return LinkedTrustSurfaceToolStatus {
            name: spec.name.to_string(),
            required: spec.required,
            status: LinkedTrustSurfaceToolStatusKind::AmbientFallback,
            path: Some(path),
            sysroot: expected_sysroot,
            bin_dir: Some(bin_dir.to_path_buf()),
            detail: Some(format!(
                "Trust toolchain has canonical `{}` but required compatibility alias binding is outside the selected same-sysroot surface: {}",
                spec.name,
                invalid_alias_bindings.join("; ")
            )),
        };
    }
    LinkedTrustSurfaceToolStatus {
        name: spec.name.to_string(),
        required: spec.required,
        status: LinkedTrustSurfaceToolStatusKind::Present,
        path: Some(path),
        sysroot: expected_sysroot,
        bin_dir: Some(bin_dir.to_path_buf()),
        detail: None,
    }
}

fn blocker_for_surface_tool(
    status: &LinkedTrustSurfaceToolStatus,
) -> Option<(LinkedTrustCargoSurfaceKind, String)> {
    match status.status {
        LinkedTrustSurfaceToolStatusKind::Present
        | LinkedTrustSurfaceToolStatusKind::OptionalMissing => None,
        LinkedTrustSurfaceToolStatusKind::Missing if !status.required => None,
        LinkedTrustSurfaceToolStatusKind::Missing => Some((
            LinkedTrustCargoSurfaceKind::Missing,
            status.detail.clone().unwrap_or_else(|| {
                format!("Trust toolchain is missing canonical `{}`", status.name)
            }),
        )),
        LinkedTrustSurfaceToolStatusKind::AmbientFallback => Some((
            LinkedTrustCargoSurfaceKind::AmbientFallback,
            status.detail.clone().unwrap_or_else(|| {
                format!("canonical `{}` resolved through ambient fallback", status.name)
            }),
        )),
    }
}

fn tool_path(tools: &[LinkedTrustSurfaceToolStatus], name: &str) -> Option<PathBuf> {
    tools.iter().find(|tool| tool.name == name).and_then(|tool| {
        (tool.status == LinkedTrustSurfaceToolStatusKind::Present)
            .then(|| tool.path.clone())
            .flatten()
    })
}
