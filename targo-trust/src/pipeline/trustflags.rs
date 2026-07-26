// TRUSTFLAGS: the sanctioned per-run override channel for -Ztrust-* options.
//
// TRUSTFLAGS is to trust verification what RUSTFLAGS is to codegen: a
// space-separated environment variable (or CARGO_ENCODED_TRUSTFLAGS,
// U+001F-separated, which takes precedence — matching Cargo's
// CARGO_ENCODED_RUSTFLAGS convention) carrying `-Ztrust-*` policy options for
// one invocation. Verified runs deliberately strip `-Ztrust-*` from inherited
// RUSTFLAGS (see backend::sanitize_inherited_z_options) so ambient shell state
// cannot silently own proof policy; TRUSTFLAGS is the explicit, validated
// front door that replaces that lost capability.
//
// Merge semantics: config-derived defaults ([trust] table + CLI) are rendered
// first, then TRUSTFLAGS options are appended, so the user override wins the
// way repeated `-Z name=value` options are last-wins in rustc. Because targo's
// verified host-boundary parser (`extract_verified_targo_host_policy`) fails
// closed on duplicate policy options, the same last-wins outcome is
// materialized by REPLACING the earlier config-derived occurrence instead of
// leaving both: the effective compiler invocation is identical and the merged
// vector still flows through the exact same RUSTFLAGS/CARGO_ENCODED_RUSTFLAGS
// path Cargo fingerprints, so a TRUSTFLAGS change re-verifies instead of
// silently reusing stale artifacts.
//
// Validation is fail-closed: every token must be a `-Ztrust-*` option in the
// verified Targo host-policy protocol, and reserved authentication/transport
// options are rejected outright. Non-trust flags are an error pointing back at
// RUSTFLAGS. Empty or absent TRUSTFLAGS is a no-op.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::HashSet;
use std::env;

use super::backend::{CargoRustflags, canonical_rustc_option_name};

pub(crate) const TRUSTFLAGS_ENV: &str = "TRUSTFLAGS";
pub(crate) const CARGO_ENCODED_TRUSTFLAGS_ENV: &str = "CARGO_ENCODED_TRUSTFLAGS";

/// The `-Z` options TRUSTFLAGS may set: the verified Targo host-policy
/// protocol (`is_verified_targo_host_policy_option` in targo's target_info.rs)
/// minus the reserved options below. Every name here must also be recognized
/// by `backend::targo_owned_z_option` so inherited RUSTFLAGS can never smuggle
/// the same option around this validation (see the consistency test).
fn is_trustflags_policy_option(name: &str) -> bool {
    matches!(
        name,
        "trust-cg-output-gate"
            | "trust-verify-ay-path"
            | "trust-verify-function-budget-ms"
            | "trust-verify-include-dependencies"
            | "trust-verify-level"
            | "trust-policy"
            | "trust-verify-profile"
            | "trust-verify-timeout-ms"
            | "trust-verify-worker-threads"
    )
}

/// Reserved options TRUSTFLAGS must never set, with the reason reported to the
/// user. These are authentication or transport-integrity infrastructure, not
/// user policy:
/// - `trust-verify-session`: targo-trust generates a fresh random nonce per
///   run; it authenticates the verification evidence stream. A caller-supplied
///   session would let stale or forged transport pass authentication.
/// - `trust-verify-crate-role` / `trust-verify-package-name`: Targo derives
///   these per compilation unit; they are never user-set.
/// - `trust-proof-artifact-root`: session-scoped private (0700) directory that
///   targo-trust provisions and reads proof evidence back from. Redirecting it
///   would sever artifact collection from the run that produced it.
/// - `trust-verify-output`: transport-integrity-critical. Evidence-grade
///   crate verification requires the structured JSON transport; a last-wins
///   `human` override would sever authenticated coverage parsing and every run
///   would fail closed with a confusing transport error instead of a policy
///   error here.
fn trustflags_reserved_reason(name: &str) -> Option<&'static str> {
    match name {
        "trust-verify-session" => {
            Some("the verification session nonce is generated per run to authenticate evidence")
        }
        "trust-verify-crate-role" | "trust-verify-package-name" => {
            Some("reserved for Targo's resolved compilation-unit metadata")
        }
        "trust-proof-artifact-root" => {
            Some("the proof artifact root is provisioned per run as a private evidence channel")
        }
        "trust-verify-output" => Some(
            "the verifier transport format is owned by targo-trust; evidence-grade runs require the structured JSON transport",
        ),
        _ => None,
    }
}

/// Sorted user-facing list for error messages.
fn supported_trustflags_options() -> &'static str {
    "-Ztrust-cg-output-gate, -Ztrust-policy, -Ztrust-verify-ay-path, \
     -Ztrust-verify-function-budget-ms, -Ztrust-verify-include-dependencies, \
     -Ztrust-verify-level, -Ztrust-verify-profile, -Ztrust-verify-timeout-ms, \
     -Ztrust-verify-worker-threads"
}

/// Validated TRUSTFLAGS `-Z` option payloads (e.g.
/// `trust-verify-function-budget-ms=60000`), deduplicated last-wins by
/// rustc-canonical option name.
#[derive(Debug, Clone, Default)]
pub(crate) struct TrustFlags {
    options: Vec<String>,
}

impl TrustFlags {
    #[cfg(test)]
    pub(crate) fn is_empty(&self) -> bool {
        self.options.is_empty()
    }

    #[cfg(test)]
    pub(crate) fn options(&self) -> &[String] {
        &self.options
    }

    /// Parse the space-separated TRUSTFLAGS protocol (Cargo's literal-space
    /// RUSTFLAGS rule: no shell quoting, empty segments dropped).
    pub(crate) fn parse_plain(flags: &str) -> Result<Self, String> {
        let tokens = flags
            .split(' ')
            .map(str::trim)
            .filter(|token| !token.is_empty())
            .map(str::to_string)
            .collect::<Vec<_>>();
        Self::parse_tokens(&tokens, TRUSTFLAGS_ENV)
    }

    /// Parse the U+001F-separated CARGO_ENCODED_TRUSTFLAGS protocol.
    pub(crate) fn parse_encoded(flags: &str) -> Result<Self, String> {
        if flags.is_empty() {
            return Ok(Self::default());
        }
        // Empty interior/trailing segments are real encoded arguments; a
        // caller that produces them is invalid rather than silently repaired.
        let tokens = flags.split('\x1f').map(str::to_string).collect::<Vec<_>>();
        Self::parse_tokens(&tokens, CARGO_ENCODED_TRUSTFLAGS_ENV)
    }

    fn parse_tokens(tokens: &[String], source: &str) -> Result<Self, String> {
        let mut options = Vec::new();
        let mut index = 0;
        while index < tokens.len() {
            let token = &tokens[index];
            let option = if token == "-Z" {
                index += 1;
                tokens
                    .get(index)
                    .ok_or_else(|| format!("{source} ends with an incomplete `-Z` option"))?
                    .as_str()
            } else if let Some(option) = token.strip_prefix("-Z").filter(|opt| !opt.is_empty()) {
                option
            } else {
                return Err(format!(
                    "{source} contains `{token}`: TRUSTFLAGS is for -Ztrust-* options; use RUSTFLAGS for codegen flags"
                ));
            };
            validate_trustflags_option(option, source)?;
            options.push(option.to_string());
            index += 1;
        }
        Ok(Self { options: dedupe_last_wins(options) })
    }

    /// Whether any option payload contains whitespace, in which case Cargo's
    /// plain space-separated RUSTFLAGS protocol cannot represent it losslessly.
    fn requires_encoded_representation(&self) -> bool {
        self.options.iter().any(|option| option.chars().any(char::is_whitespace))
    }

    /// Merge into an assembled rustc argument vector: remove every existing
    /// spelling of an overridden option, then append the TRUSTFLAGS value.
    /// See the module docs for why replacement (not plain append) carries the
    /// last-wins semantics across targo's duplicate-rejecting host boundary.
    pub(crate) fn apply_to_args(&self, args: &mut Vec<String>) {
        if self.options.is_empty() {
            return;
        }
        let overridden = self
            .options
            .iter()
            .map(|option| canonical_rustc_option_name(option).into_owned())
            .collect::<HashSet<_>>();
        let mut merged = Vec::with_capacity(args.len() + 2 * self.options.len());
        let mut index = 0;
        while index < args.len() {
            if args[index] == "-Z"
                && args.get(index + 1).is_some_and(|option| {
                    overridden.contains(canonical_rustc_option_name(option).as_ref())
                })
            {
                index += 2;
                continue;
            }
            if args[index].strip_prefix("-Z").filter(|option| !option.is_empty()).is_some_and(
                |option| overridden.contains(canonical_rustc_option_name(option).as_ref()),
            ) {
                index += 1;
                continue;
            }
            merged.push(args[index].clone());
            index += 1;
        }
        for option in &self.options {
            merged.push("-Z".to_string());
            merged.push(option.clone());
        }
        *args = merged;
    }

    /// Merge into the fully assembled Cargo rustflags (config-derived policy
    /// plus verification controls), preserving the representation except when
    /// a whitespace-bearing encoded TRUSTFLAGS value forces Cargo's lossless
    /// encoded protocol — the same rule `cargo_rustflags_with_controls` uses.
    pub(crate) fn apply_to_cargo_rustflags(&self, merged: CargoRustflags) -> CargoRustflags {
        if self.options.is_empty() {
            return merged;
        }
        match merged {
            CargoRustflags::Plain(flags) => {
                let mut args = flags
                    .split(' ')
                    .map(str::trim)
                    .filter(|arg| !arg.is_empty())
                    .map(str::to_string)
                    .collect::<Vec<_>>();
                self.apply_to_args(&mut args);
                if self.requires_encoded_representation() {
                    CargoRustflags::Encoded(args.join("\x1f"))
                } else {
                    CargoRustflags::Plain(args.join(" "))
                }
            }
            CargoRustflags::Encoded(flags) => {
                let mut args = if flags.is_empty() {
                    Vec::new()
                } else {
                    flags.split('\x1f').map(str::to_string).collect::<Vec<_>>()
                };
                self.apply_to_args(&mut args);
                CargoRustflags::Encoded(args.join("\x1f"))
            }
        }
    }
}

fn validate_trustflags_option(option: &str, source: &str) -> Result<(), String> {
    if option.contains('\x1f') {
        return Err(format!(
            "{source} option values cannot contain Cargo's U+001F encoded-rustflags delimiter"
        ));
    }
    let name = canonical_rustc_option_name(option);
    if let Some(reason) = trustflags_reserved_reason(&name) {
        return Err(format!("{source} cannot set -Z{name}: {reason}"));
    }
    if is_trustflags_policy_option(&name) {
        return Ok(());
    }
    if name.starts_with("trust-") || name.starts_with("no-trust-") {
        return Err(format!(
            "{source} contains -Z{name}, which is not a supported TRUSTFLAGS policy option; supported options: {}",
            supported_trustflags_options()
        ));
    }
    Err(format!(
        "{source} contains `-Z{option}`: TRUSTFLAGS is for -Ztrust-* options; use RUSTFLAGS for codegen flags"
    ))
}

/// Deduplicate by rustc-canonical option name, keeping the LAST occurrence
/// (rustc's own semantics for repeated `-Z name=value`), preserving the
/// relative order of the surviving occurrences.
fn dedupe_last_wins(options: Vec<String>) -> Vec<String> {
    let mut seen = HashSet::new();
    let mut deduped = options
        .into_iter()
        .rev()
        .filter(|option| seen.insert(canonical_rustc_option_name(option).into_owned()))
        .collect::<Vec<_>>();
    deduped.reverse();
    deduped
}

/// Read and validate TRUSTFLAGS at invocation start, fail-closed: an invalid
/// value is an error before any compiler is spawned, never a silently ignored
/// policy. CARGO_ENCODED_TRUSTFLAGS takes precedence over TRUSTFLAGS the way
/// CARGO_ENCODED_RUSTFLAGS takes precedence over RUSTFLAGS in Cargo.
pub(crate) fn trustflags_from_env() -> Result<TrustFlags, String> {
    if let Some(encoded) = env::var_os(CARGO_ENCODED_TRUSTFLAGS_ENV) {
        let encoded = encoded.to_str().ok_or_else(|| {
            format!(
                "{CARGO_ENCODED_TRUSTFLAGS_ENV} is not valid Unicode; verified runs cannot preserve its compiler-argument boundaries"
            )
        })?;
        return TrustFlags::parse_encoded(encoded);
    }
    if let Some(plain) = env::var_os(TRUSTFLAGS_ENV) {
        let plain = plain.to_str().ok_or_else(|| {
            format!(
                "{TRUSTFLAGS_ENV} is not valid Unicode; verified runs cannot preserve its compiler-argument boundaries"
            )
        })?;
        return TrustFlags::parse_plain(plain);
    }
    Ok(TrustFlags::default())
}

#[cfg(test)]
mod tests {
    use super::super::backend::targo_owned_z_option;
    use super::*;

    #[test]
    fn empty_or_absent_trustflags_are_a_no_op() {
        for parsed in [
            TrustFlags::parse_plain("").expect("empty plain"),
            TrustFlags::parse_plain("   ").expect("blank plain"),
            TrustFlags::parse_encoded("").expect("empty encoded"),
            TrustFlags::default(),
        ] {
            assert!(parsed.is_empty());
            let mut args = vec!["-Z".to_string(), "trust-verify-level=2".to_string()];
            let untouched = args.clone();
            parsed.apply_to_args(&mut args);
            assert_eq!(args, untouched);
            let CargoRustflags::Plain(plain) =
                parsed.apply_to_cargo_rustflags(CargoRustflags::Plain("-C opt-level=2".into()))
            else {
                panic!("no-op must preserve the plain representation");
            };
            assert_eq!(plain, "-C opt-level=2");
        }
    }

    #[test]
    fn accepts_compact_split_and_rustc_equivalent_spellings() {
        let parsed = TrustFlags::parse_plain(
            "-Ztrust-verify-function-budget-ms=60000 -Z trust-verify-level=1 \
             -Ztrust_policy=advisory",
        )
        .expect("supported policy options parse");
        assert_eq!(
            parsed.options(),
            [
                "trust-verify-function-budget-ms=60000",
                "trust-verify-level=1",
                "trust_policy=advisory"
            ]
        );
    }

    #[test]
    fn duplicate_options_are_last_wins_across_equivalent_spellings() {
        let parsed =
            TrustFlags::parse_plain("-Ztrust-verify-level=0 -Ztrust-policy=advisory -Z trust_verify_level=2")
                .expect("duplicates resolve last-wins");
        assert_eq!(parsed.options(), ["trust-policy=advisory", "trust_verify_level=2"]);
    }

    #[test]
    fn non_trust_flags_are_rejected_toward_rustflags() {
        for flags in ["-Copt-level=3", "--cfg feature", "-Zthreads=8", "opt-level=3", "-Z"] {
            let error = TrustFlags::parse_plain(flags)
                .expect_err("non-trust TRUSTFLAGS content must fail closed");
            assert!(
                error.contains("use RUSTFLAGS for codegen flags")
                    || error.contains("incomplete `-Z` option"),
                "{flags}: {error}"
            );
        }
    }

    #[test]
    fn reserved_authentication_and_transport_options_are_rejected() {
        for (flag, needle) in [
            ("-Ztrust-verify-session=forged", "generated per run"),
            ("-Z trust-verify-session=forged", "generated per run"),
            ("-Ztrust_verify_session=forged", "generated per run"),
            ("-Ztrust-verify-crate-role=primary", "compilation-unit metadata"),
            ("-Ztrust-verify-package-name=forged", "compilation-unit metadata"),
            ("-Ztrust-proof-artifact-root=/tmp/forged", "provisioned per run"),
            ("-Ztrust-verify-output=human", "structured JSON transport"),
        ] {
            let error =
                TrustFlags::parse_plain(flag).expect_err("reserved options must fail closed");
            assert!(error.contains(needle), "{flag}: {error}");
            assert!(error.contains("cannot set"), "{flag}: {error}");
        }
    }

    #[test]
    fn unsupported_trust_options_list_the_supported_policy_surface() {
        for flag in
            ["-Ztrust-dump=mir-only:/tmp/d", "-Ztrust-verify=off", "-Ztrust-verify=off", "-Ztrust-ir-flip"]
        {
            let error = TrustFlags::parse_plain(flag)
                .expect_err("non-policy trust options must fail closed");
            assert!(error.contains("not a supported TRUSTFLAGS policy option"), "{flag}: {error}");
            assert!(error.contains("trust-verify-function-budget-ms"), "{flag}: {error}");
        }
    }

    #[test]
    fn encoded_trustflags_reject_empty_segments_and_accept_spaced_values() {
        assert!(TrustFlags::parse_encoded("-Ztrust-policy=advisory\x1f").is_err());
        let parsed = TrustFlags::parse_encoded("-Z\x1ftrust-verify-ay-path=/tmp/solver tools/ay")
            .expect("encoded values may contain spaces");
        assert_eq!(parsed.options(), ["trust-verify-ay-path=/tmp/solver tools/ay"]);
        assert!(parsed.requires_encoded_representation());
    }

    #[test]
    fn override_replaces_the_config_derived_occurrence_and_appends_last() {
        let parsed = TrustFlags::parse_plain("-Ztrust-verify-function-budget-ms=60000")
            .expect("budget override parses");
        let mut args = vec![
            "-Z".to_string(),
            "trust-verify-timeout-ms=5000".to_string(),
            "-Z".to_string(),
            "trust-verify-function-budget-ms=120000".to_string(),
            "-Ztrust_verify_function_budget_ms=90000".to_string(),
            "-Z".to_string(),
            "trust-verify-session=nonce".to_string(),
        ];
        parsed.apply_to_args(&mut args);
        assert_eq!(
            args,
            [
                "-Z",
                "trust-verify-timeout-ms=5000",
                "-Z",
                "trust-verify-session=nonce",
                "-Z",
                "trust-verify-function-budget-ms=60000",
            ]
        );
    }

    #[test]
    fn cargo_rustflags_merge_preserves_representation_and_unrelated_flags() {
        let parsed =
            TrustFlags::parse_plain("-Ztrust-verify-level=0").expect("level override parses");
        let CargoRustflags::Plain(plain) = parsed.apply_to_cargo_rustflags(CargoRustflags::Plain(
            "-C opt-level=2 -Z trust-verify-level=2 -Z trust-verify-output=json".to_string(),
        )) else {
            panic!("space-free overrides keep the plain representation");
        };
        assert_eq!(plain, "-C opt-level=2 -Z trust-verify-output=json -Z trust-verify-level=0");

        let CargoRustflags::Encoded(encoded) = parsed.apply_to_cargo_rustflags(
            CargoRustflags::Encoded("-C\x1fopt-level=2\x1f-Ztrust-verify-level=2".to_string()),
        ) else {
            panic!("encoded input keeps the encoded representation");
        };
        assert_eq!(encoded, "-C\x1fopt-level=2\x1f-Z\x1ftrust-verify-level=0");
    }

    #[test]
    fn spaced_encoded_override_forces_the_lossless_encoded_representation() {
        let parsed = TrustFlags::parse_encoded("-Ztrust-verify-ay-path=/tmp/solver tools/ay")
            .expect("spaced solver path parses");
        let CargoRustflags::Encoded(encoded) =
            parsed.apply_to_cargo_rustflags(CargoRustflags::Plain("-C opt-level=2".to_string()))
        else {
            panic!("a spaced override cannot remain in the plain representation");
        };
        assert_eq!(encoded, "-C\x1fopt-level=2\x1f-Z\x1ftrust-verify-ay-path=/tmp/solver tools/ay");
    }

    #[test]
    fn every_trustflags_name_is_stripped_from_inherited_rustflags() {
        // TRUSTFLAGS is only a sound single control plane if inherited
        // RUSTFLAGS can never carry the same options into a verified build
        // (or the reserved authentication options around this validation).
        for name in [
            "trust-cg-output-gate",
            "trust-policy",
            "trust-verify-ay-path",
            "trust-verify-function-budget-ms",
            "trust-verify-include-dependencies",
            "trust-verify-level",
            "trust-verify-profile",
            "trust-verify-timeout-ms",
            "trust-verify-worker-threads",
            "trust-verify-session",
            "trust-verify-crate-role",
            "trust-verify-package-name",
            "trust-proof-artifact-root",
            "trust-verify-output",
        ] {
            assert!(
                is_trustflags_policy_option(name) ^ trustflags_reserved_reason(name).is_some(),
                "{name} must be exactly one of allowed/reserved"
            );
            assert!(
                targo_owned_z_option(name, false),
                "{name} must be sanitized out of inherited RUSTFLAGS"
            );
        }
    }
}
