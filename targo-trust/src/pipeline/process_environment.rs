//! Environment authority boundary for proof compiler subprocesses.

use std::env;
use std::ffi::{OsStr, OsString};
use std::process::Command;

/// Retired ambient controls that must never become a second, untracked proof
/// policy beside the authenticated compiler arguments. In particular,
/// `TRUST_NO_VERIFY=1` is translated by the compiler driver into a final
/// `-Ztrust-verify=off`, so inheriting it would override Targo's verified argv.
const PROOF_COMPILER_AUTHORITY_ENV: &[&str] = &[
    "TRUST_VERIFY",
    "AY_DIRECT_SOLVE_TIMEOUT_MS",
    "AY_PATH",
    "TY_PATH",
    "TRUST_AY_PATH",
    "TRUST_AGGREGATE_PERTURB",
    "TRUST_BACKING_INVARIANTS",
    "TRUST_BRIDGE_GATE",
    "TRUST_CACHE_DIR",
    "TRUST_CALLEE_PERTURB",
    "TRUST_COMPILER_CACHE",
    "TRUST_DUMP_ONLY",
    "TRUST_HARDENED",
    "TRUST_INTERIOR_PERTURB",
    "TRUST_IR_FLIP",
    "TRUST_NATIVE_UNIVERSAL",
    "TRUST_NO_COMPILER_CACHE",
    "TRUST_NO_VERIFY",
    "TRUST_PROFILE",
    "TRUST_PROP_UNSAT_WORK_BUDGET",
    "TRUST_PROVE_BUDGET_SECS",
    "TRUST_SOLVER",
    "TRUST_SPINE_CONTRACT_FLIP",
    "TRUST_SPINE_NATIVE_GEN",
    "TRUST_SPINE_VERDICT_FLIP",
    "TRUST_STRUCTFIELD_PERTURB",
    "TRUST_TEMPORAL_SINGLE_WRITER",
    "TRUST_TYPE_LOWERING_PRODUCED_NODE_BUDGET",
    "TRUST_TY_PATH",
    "TRUST_VCGEN_BUNDLE_ADT_BUDGET",
    "TRUST_VCGEN_GENERATION_WORK_BUDGET",
    "TRUST_VCGEN_WORK_BUDGET",
    "TRUST_VERIFY_FN_BUDGET_MS",
    "TRUST_VERIFY_HARDENED",
    "TRUST_VERIFY_INCLUDE_DEPENDENCIES",
    "TRUST_VERIFY_INCLUDE_GENERATED",
    "TRUST_VERIFY_MEMORY_SAFE",
    "TRUST_VERIFY_OUTPUT",
    "TRUST_VERIFY_POLICY",
    "TRUST_VERIFY_PRIMARY_ONLY",
    "TRUST_VERIFY_SURVEY",
    "TRUST_VERIFY_TIMEOUT_MS",
    "TRUST_VERIFY_WORKER_THREADS",
    "TRUST_WP_PATH",
    "TRUST_WAVE24_PERTURB",
];

fn is_proof_compiler_authority_env(name: &OsStr) -> bool {
    let Some(name) = name.to_str() else { return false };
    PROOF_COMPILER_AUTHORITY_ENV.iter().any(|authority| name.eq_ignore_ascii_case(authority))
}

/// Remove proof authority from both the inherited process environment and any
/// entries already staged on `command`.
///
/// Windows environment names are case-insensitive but case-preserving. Sweep
/// the names actually present, as well as every canonical spelling, so a
/// mixed-case inherited or explicitly staged alias cannot survive on any host.
pub(super) fn scrub_proof_compiler_authority_env(command: &mut Command) {
    let aliases = env::vars_os()
        .map(|(name, _)| name)
        .chain(command.get_envs().map(|(name, _)| name.to_os_string()))
        .filter(|name| is_proof_compiler_authority_env(name))
        .collect::<Vec<OsString>>();

    for name in PROOF_COMPILER_AUTHORITY_ENV {
        command.env_remove(name);
    }
    for alias in aliases {
        command.env_remove(alias);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn proof_compiler_authority_scrub_is_case_insensitive() {
        let aliases = ["TRUST_NO_VERIFY", "trust_no_verify", "TrUsT_No_Verify"];
        let mut command = Command::new("unused-test-program");
        for alias in aliases {
            command.env(alias, "1");
            assert!(is_proof_compiler_authority_env(OsStr::new(alias)));
        }

        scrub_proof_compiler_authority_env(&mut command);

        let retained = command
            .get_envs()
            .filter(|(name, _)| is_proof_compiler_authority_env(name))
            .collect::<Vec<_>>();
        assert!(!retained.is_empty(), "the scrub should record environment removals");
        assert!(
            retained.iter().all(|(_, value)| value.is_none()),
            "no case variant may retain a value: {retained:?}"
        );
    }
}
