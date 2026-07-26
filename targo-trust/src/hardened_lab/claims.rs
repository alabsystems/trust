use serde::Serialize;

use super::validate::{validate_byte_utf8_walkthrough, validate_path_identity_walkthrough};
use super::validate_additional::validate_additional_walkthroughs;
use crate::source_analysis::VcKind;

pub(super) struct WalkthroughSpec {
    pub(super) name: &'static str,
    pub(super) validate: fn(&str) -> Vec<String>,
}

#[derive(Debug, Clone, Copy)]
pub(super) struct WalkthroughEvidenceSpec {
    pub(super) bin: &'static str,
    pub(super) requirements: &'static [TranscriptRequirement],
}

#[derive(Debug, Clone, Copy, Serialize)]
pub(super) struct TranscriptRequirement {
    pub(super) key: &'static str,
    pub(super) value: &'static str,
}

pub(super) const WALKTHROUGH_SPECS: &[WalkthroughSpec] = &[
    WalkthroughSpec { name: "additional_walkthroughs", validate: validate_additional_walkthroughs },
    WalkthroughSpec { name: "byte_utf8_walkthrough", validate: validate_byte_utf8_walkthrough },
    WalkthroughSpec { name: "path_identity_toctou", validate: validate_path_identity_walkthrough },
];

#[derive(Debug, Clone, Copy)]
pub(super) struct ClaimSpec {
    pub(super) id: &'static str,
    pub(super) category: &'static str,
    pub(super) report_label: &'static str,
    pub(super) title: &'static str,
    pub(super) kind: VcKind,
    pub(super) required_fragment: Option<&'static str>,
    pub(super) source_example: &'static str,
    pub(super) source_reference: &'static str,
    pub(super) walkthrough_evidence: &'static [WalkthroughEvidenceSpec],
}

pub(super) const CLAIMS: &[ClaimSpec] = &[
    ClaimSpec {
        id: "path-re-resolution",
        category: "raw_path_api",
        report_label: "raw path API",
        title: "raw path APIs can re-resolve attacker-controlled names",
        kind: VcKind::HardenedRawPathApi,
        required_fragment: Some("raw path"),
        source_example: "raw_path_toctou_boundary",
        source_reference: "Corrode: Don't trust a path across two syscalls; HN: openat/capability-style filesystem APIs",
        walkthrough_evidence: &[WalkthroughEvidenceSpec {
            bin: "additional_walkthroughs",
            requirements: &[
                TranscriptRequirement { key: "walkthrough", value: "raw_path_re_resolution" },
                TranscriptRequirement { key: "raw_path_re_resolved", value: "yes" },
                TranscriptRequirement {
                    key: "raw_path_scope",
                    value: "metadata,canonicalize,symlink,rename,read",
                },
            ],
        }],
    },
    ClaimSpec {
        id: "path-identity",
        category: "path_identity",
        report_label: "path identity",
        title: "path spelling and canonicalization are not filesystem identity",
        kind: VcKind::HardenedPathIdentity,
        required_fragment: Some("identity"),
        source_example: "path_identity_boundary",
        source_reference: "Corrode: preserve-root bypasses such as /../, /./, symlinks, and rm ./",
        walkthrough_evidence: &[WalkthroughEvidenceSpec {
            bin: "path_identity_toctou",
            requirements: &[
                TranscriptRequirement { key: "walkthrough", value: "path_identity_toctou" },
                TranscriptRequirement { key: "observed", value: "swapped" },
                TranscriptRequirement { key: "result", value: "toctou-demonstrated" },
            ],
        }],
    },
    ClaimSpec {
        id: "permission-create",
        category: "permission_create",
        report_label: "permission creation",
        title: "path-based creation needs mode and parent identity evidence",
        kind: VcKind::HardenedPermissionCreate,
        required_fragment: Some("creation"),
        source_example: "permission_create_boundary",
        source_reference: "Corrode: create directories/files with final permissions, not repair after creation",
        walkthrough_evidence: &[WalkthroughEvidenceSpec {
            bin: "additional_walkthroughs",
            requirements: &[
                TranscriptRequirement { key: "walkthrough", value: "permissions" },
                TranscriptRequirement { key: "create_parent_identity_verified", value: "yes" },
                TranscriptRequirement { key: "create_new_requested_mode", value: "0o600" },
                TranscriptRequirement { key: "create_new_group_other_bits", value: "0o000" },
            ],
        }],
    },
    ClaimSpec {
        id: "permission-change",
        category: "permission_change",
        report_label: "permission change",
        title: "path-based chmod/chown needs stable identity evidence",
        kind: VcKind::HardenedPermissionChange,
        required_fragment: Some("permission"),
        source_example: "permission_window_boundary",
        source_reference: "Corrode/HN: chmod/chown by path must not race a mutable name",
        walkthrough_evidence: &[WalkthroughEvidenceSpec {
            bin: "additional_walkthroughs",
            requirements: &[
                TranscriptRequirement { key: "walkthrough", value: "permissions" },
                TranscriptRequirement { key: "chmod_identity_stable", value: "yes" },
                TranscriptRequirement { key: "chmod_window_start_mode", value: "0o644" },
                TranscriptRequirement { key: "chmod_window_final_mode", value: "0o600" },
                TranscriptRequirement { key: "chmod_change_observed", value: "yes" },
            ],
        }],
    },
    ClaimSpec {
        id: "permission-window",
        category: "permission_window",
        report_label: "permission repair window",
        title: "create-then-permission-repair opens a privilege window",
        kind: VcKind::HardenedPermissionWindow,
        required_fragment: Some("creation at line"),
        source_example: "permission_window_boundary",
        source_reference: "Corrode: set permissions at creation time, not after",
        walkthrough_evidence: &[WalkthroughEvidenceSpec {
            bin: "additional_walkthroughs",
            requirements: &[
                TranscriptRequirement { key: "walkthrough", value: "permissions" },
                TranscriptRequirement {
                    key: "result",
                    value: "permission-window-create-change-demonstrated",
                },
            ],
        }],
    },
    ClaimSpec {
        id: "byte-loss",
        category: "byte_loss",
        report_label: "byte-exact data",
        title: "lossy UTF-8 conversions corrupt byte-exact Unix data",
        kind: VcKind::HardenedByteLoss,
        required_fragment: Some("lossy"),
        source_example: "byte_exact_boundary",
        source_reference: "Corrode: comm and from_utf8_lossy; HN: byte streams are not strings",
        walkthrough_evidence: &[WalkthroughEvidenceSpec {
            bin: "byte_utf8_walkthrough",
            requirements: &[
                TranscriptRequirement { key: "walkthrough", value: "byte_utf8" },
                TranscriptRequirement {
                    key: "filename_hex",
                    value: "6e6f6e5f757466385fff5f6e616d65",
                },
                TranscriptRequirement { key: "payload_hex", value: "7061796c6f61643af0288c280a" },
                TranscriptRequirement { key: "lossy_payload_had_replacement", value: "yes" },
                TranscriptRequirement { key: "result", value: "non-utf8-demonstrated" },
            ],
        }],
    },
    ClaimSpec {
        id: "strict-utf8",
        category: "utf8_reject",
        report_label: "strict UTF-8 boundary",
        title: "strict UTF-8 conversion rejects valid Unix paths or streams",
        kind: VcKind::HardenedUtf8Boundary,
        required_fragment: Some("UTF-8"),
        source_example: "byte_exact_boundary",
        source_reference: "Corrode: sort --files0-from non-UTF-8 filename panic/rejection",
        walkthrough_evidence: &[WalkthroughEvidenceSpec {
            bin: "byte_utf8_walkthrough",
            requirements: &[
                TranscriptRequirement { key: "walkthrough", value: "byte_utf8" },
                TranscriptRequirement { key: "strict_filename_utf8", value: "error" },
                TranscriptRequirement { key: "read_to_string_error", value: "InvalidData" },
                TranscriptRequirement { key: "roundtrip_payload_bytes", value: "ok" },
            ],
        }],
    },
    ClaimSpec {
        id: "panic-dos",
        category: "panic_boundary",
        report_label: "panic boundary",
        title: "panic, unwrap, expect, assert, and unreachable paths are DoS boundaries",
        kind: VcKind::HardenedPanic,
        required_fragment: Some("panic"),
        source_example: "panic_boundary",
        source_reference: "Corrode: every panic in attacker-shaped CLI input is a denial-of-service path",
        walkthrough_evidence: &[WalkthroughEvidenceSpec {
            bin: "additional_walkthroughs",
            requirements: &[
                TranscriptRequirement { key: "walkthrough", value: "panic_boundary" },
                TranscriptRequirement { key: "caught_panic_count", value: "6" },
                TranscriptRequirement { key: "panic_payloads_escaped", value: "no" },
            ],
        }],
    },
    ClaimSpec {
        id: "error-discard",
        category: "error_discard",
        report_label: "discarded error",
        title: "discarded errors hide failed writes, chmod/chown failures, or status aggregation",
        kind: VcKind::HardenedErrorDiscard,
        required_fragment: Some("discard"),
        source_example: "discarded_error_boundary",
        source_reference: "Corrode: dd set_len .ok(), chmod/chown worst-exit aggregation",
        walkthrough_evidence: &[WalkthroughEvidenceSpec {
            bin: "additional_walkthroughs",
            requirements: &[
                TranscriptRequirement { key: "walkthrough", value: "error_discard_integrity" },
                TranscriptRequirement { key: "discarded_read_error", value: "lost" },
                TranscriptRequirement { key: "integrity_check", value: "discard-changes-decision" },
            ],
        }],
    },
    ClaimSpec {
        id: "compatibility-oracle",
        category: "compat_observable",
        report_label: "observable compatibility",
        title: "GNU/POSIX observable compatibility is a safety property",
        kind: VcKind::HardenedCompatibility,
        required_fragment: Some("CLI boundary"),
        source_example: "compatibility_observable_boundary",
        source_reference: "Corrode: kill -1, rm ./, exit codes/messages; HN: differential fuzzing needs structured semantics",
        walkthrough_evidence: &[WalkthroughEvidenceSpec {
            bin: "additional_walkthroughs",
            requirements: &[
                TranscriptRequirement { key: "walkthrough", value: "cli_args" },
                TranscriptRequirement { key: "cli_child_mode", value: "args_os" },
                TranscriptRequirement { key: "cli_child_invalid_arg_to_str", value: "none" },
            ],
        }],
    },
    ClaimSpec {
        id: "process-signal-semantics",
        category: "process_semantics",
        report_label: "process/SIGPIPE semantics",
        title: "startup, stdout, and SIGPIPE behavior are compatibility-sensitive",
        kind: VcKind::HardenedProcessSemantics,
        required_fragment: Some("SIGPIPE"),
        source_example: "process_signal_semantics_boundary",
        source_reference: "HN: Rust changes inherited SIGPIPE/default process semantics before main, which matters for coreutils-compatible tools",
        walkthrough_evidence: &[WalkthroughEvidenceSpec {
            bin: "additional_walkthroughs",
            requirements: &[
                TranscriptRequirement { key: "walkthrough", value: "process_sigpipe" },
                TranscriptRequirement { key: "closed_stream_write_error", value: "BrokenPipe" },
                TranscriptRequirement { key: "broken_pipe_handled", value: "ok" },
            ],
        }],
    },
    ClaimSpec {
        id: "trust-boundary",
        category: "trust_domain",
        report_label: "trust-domain boundary",
        title: "root, privilege, name-service, and dynamic-loading effects need trust-state models",
        kind: VcKind::HardenedTrustBoundary,
        required_fragment: None,
        source_example: "trust_domain_ordering_boundary",
        source_reference: "Corrode: chroot --userspec, NSS, dlopen, setuid/setgid ordering",
        walkthrough_evidence: &[WalkthroughEvidenceSpec {
            bin: "additional_walkthroughs",
            requirements: &[
                TranscriptRequirement { key: "walkthrough", value: "trust_domain_order" },
                TranscriptRequirement {
                    key: "pre_privilege_probe_order",
                    value: "root,user,group,plugin",
                },
                TranscriptRequirement { key: "privileged_ops_mode", value: "simulated" },
                TranscriptRequirement {
                    key: "evidence_scope",
                    value: "rootless_preflight_and_trace_order",
                },
            ],
        }],
    },
    ClaimSpec {
        id: "trust-domain-order",
        category: "trust_domain_order",
        report_label: "trust-domain ordering",
        title: "source inventory flags name-service or dynamic loading after a trust-domain transition",
        kind: VcKind::HardenedTrustDomainOrder,
        required_fragment: Some("after chroot"),
        source_example: "trust_domain_ordering_boundary",
        source_reference: "Corrode: resolve users/groups before crossing the chroot trust boundary",
        walkthrough_evidence: &[WalkthroughEvidenceSpec {
            bin: "additional_walkthroughs",
            requirements: &[
                TranscriptRequirement { key: "walkthrough", value: "trust_domain_order" },
                TranscriptRequirement { key: "safe_trace_late_lookups", value: "0" },
                TranscriptRequirement { key: "unsafe_trace_late_lookups", value: "6" },
                TranscriptRequirement { key: "root_transition_effect", value: "not_exercised" },
            ],
        }],
    },
    ClaimSpec {
        id: "unsafe-operation",
        category: "unsafe_operation",
        report_label: "unsafe operation inventory",
        title: "unsafe blocks and raw-pointer operations require trusted-wrapper evidence",
        kind: VcKind::HardenedUnsafeOperation,
        required_fragment: Some("trusted-wrapper"),
        source_example: "unsafe_ffi_boundary",
        source_reference: "HN: Rust's guarantees end at unsafe/FFI unless wrappers state and prove their contracts",
        walkthrough_evidence: &[WalkthroughEvidenceSpec {
            bin: "additional_walkthroughs",
            requirements: &[
                TranscriptRequirement {
                    key: "walkthrough",
                    value: "unsafe_ffi_boundary_inventory",
                },
                TranscriptRequirement { key: "unsafe_pointer_probe", value: "ok" },
                TranscriptRequirement { key: "unsafe_block_count", value: "1" },
            ],
        }],
    },
    ClaimSpec {
        id: "ffi-boundary",
        category: "ffi_boundary",
        report_label: "extern FFI declaration inventory",
        title: "extern FFI declarations are inventory until ABI and memory trust evidence exists",
        kind: VcKind::HardenedFfiBoundary,
        required_fragment: Some("extern boundary"),
        source_example: "main",
        source_reference: "HN: Rust's guarantees end at unsafe/FFI unless wrappers state and prove their contracts",
        walkthrough_evidence: &[WalkthroughEvidenceSpec {
            bin: "additional_walkthroughs",
            requirements: &[
                TranscriptRequirement { key: "walkthrough", value: "ffi_boundary_inventory" },
                TranscriptRequirement { key: "ffi_declared", value: "getenv,strlen" },
                TranscriptRequirement { key: "ffi_called", value: "getenv,strlen" },
                TranscriptRequirement { key: "ffi_call_count", value: "2" },
            ],
        }],
    },
];
