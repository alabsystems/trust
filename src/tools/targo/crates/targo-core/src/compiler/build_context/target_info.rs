//! This modules contains types storing information of target platforms.
//!
//! Normally, call [`RustcTargetData::new`] to construct all the target
//! platform once, and then query info on your demand. For example,
//!
//! * [`RustcTargetData::dep_platform_activated`] to check if platform is activated.
//! * [`RustcTargetData::info`] to get a [`TargetInfo`] for an in-depth query.
//! * [`TargetInfo::rustc_outputs`] to get a list of supported file types.

use crate::compiler::CompileKind;
use crate::compiler::CompileMode;
use crate::compiler::CompileTarget;
use crate::compiler::CrateType;
use crate::compiler::TRUST_TARGO_LANE_RUSTFLAGS_ENV;
use crate::compiler::apply_env_config;
use crate::context::{GlobalContext, OptValue, StringList, TargetConfig};
use crate::util::interning::InternedString;
use crate::util::rustc_options::{canonical_codegen_backend_value, rustc_option_parts};
use crate::util::{CargoResult, Rustc};
use crate::workspace::{Dependency, Package, Target, TargetKind, Workspace};

use anyhow::Context as _;
use cargo_platform::{Cfg, CfgExpr};
use cargo_util::ProcessBuilder;
use serde::Deserialize;

use crate::util::data_structures::{HashMap, HashSet};
use std::cell::RefCell;
use std::collections::hash_map::Entry;
use std::ffi::OsStr;
use std::path::PathBuf;
use std::rc::Rc;
use std::str::{self, FromStr};

const RUST_TARGET_PATH_ENV: &str = "RUST_TARGET_PATH";

// Trust: a target specification decides layout, ABI, and codegen options, so it
// is a semantic input to every proof this build produces. Upstream lets a named
// target resolve through `RUST_TARGET_PATH` and a sysroot search, which has no
// authenticated origin and no content binding — the same name can mean
// different things on two machines. Verified builds therefore accept only the
// compiler's own built-in inventory or an explicit JSON file Cargo has hashed.
fn verified_targo_named_target_error(
    kind: CompileKind,
    compiler_host: &str,
    compiler_builtin_targets: &str,
) -> Option<String> {
    let target = match kind {
        // An omitted --target is still parsed by rustc as its host TargetTuple,
        // and a dishonest/nonstandard host string could otherwise enter the same
        // sysroot fallback. Bind it to the compiler's built-in inventory too.
        CompileKind::Host => compiler_host,
        CompileKind::Target(CompileTarget::Tuple(target)) => target.as_str(),
        // An explicit JSON target is authenticated by Cargo's byte digest and
        // rustc's captured parse contents.
        CompileKind::Target(CompileTarget::Json { .. }) => return None,
    };
    if compiler_builtin_targets
        .lines()
        .any(|builtin| builtin == target)
    {
        return None;
    }
    Some(format!(
        "verified Targo rejects named non-built-in target `{target}`: RUST_TARGET_PATH and sysroot custom-target fallback have no authenticated origin or content binding; pass an explicit .json --target with -Zjson-target-spec"
    ))
}

fn validate_verified_targo_target_origin(rustc: &Rustc, kind: CompileKind) -> CargoResult<()> {
    if !super::super::verified_targo_protocol_active()
        || matches!(kind, CompileKind::Target(CompileTarget::Json { .. }))
    {
        return Ok(());
    }

    // Ask the exact selected compiler for its closed built-in set without a
    // Cargo/compiler wrapper or ambient named-target search path. Exact line
    // membership is an origin check, not a suffix/shape heuristic. The compiler
    // independently enforces its static built-in allowlist before Target::search,
    // so this Cargo check is early diagnostics rather than the sole boundary.
    let mut process = rustc.process_no_wrapper();
    rustc.configure_verified_loader_environment(&mut process)?;
    process
        .arg("--print=target-list")
        .env_remove(RUST_TARGET_PATH_ENV);
    let output = crate::context::compiler_query::exec(&process)
        .context("failed to query the selected compiler's exact built-in target inventory")?;
    let builtin_targets = String::from_utf8(output.stdout)
        .context("the selected compiler's built-in target inventory was not valid UTF-8")?;
    if let Some(error) = verified_targo_named_target_error(kind, &rustc.host, &builtin_targets) {
        anyhow::bail!(error);
    }
    Ok(())
}

/// Information about the platform target gleaned from querying rustc.
///
/// [`RustcTargetData`] keeps several of these, one for the host and the others
/// for other specified targets. If no target is specified, it uses a clone from
/// the host.
#[derive(Clone)]
pub struct TargetInfo {
    /// A base process builder for discovering crate type information. In
    /// particular, this is used to determine the output filename prefix and
    /// suffix for a crate type.
    crate_type_process: ProcessBuilder,
    /// Cache of output filename prefixes and suffixes.
    ///
    /// The key is the crate type name (like `cdylib`) and the value is
    /// `Some((prefix, suffix))`, for example `libcargo.so` would be
    /// `Some(("lib", ".so"))`. The value is `None` if the crate type is not
    /// supported.
    crate_types: RefCell<HashMap<CrateType, Option<(String, String)>>>,
    /// `cfg` information extracted from `rustc --print=cfg`.
    cfg: Vec<Cfg>,
    /// `supports_std` information extracted from `rustc --print=target-spec-json`
    pub supports_std: Option<bool>,
    /// Supported values for `-Csplit-debuginfo=` flag, queried from rustc
    support_split_debuginfo: Vec<String>,
    /// Path to the sysroot.
    pub sysroot: PathBuf,
    /// Path to the "lib" directory in the sysroot which rustc uses for linking
    /// target libraries.
    pub sysroot_target_libdir: PathBuf,
    /// Extra flags to pass to `rustc`, see [`extra_args`].
    pub rustflags: Rc<[String]>,
    /// Extra flags to pass to `rustdoc`, see [`extra_args`].
    pub rustdocflags: Rc<[String]>,
    /// Should metadata be embedded in .rlib files?
    /// Corresponds to `-Zembed-metadata`.
    pub should_embed_metadata: bool,
}

/// Kind of each file generated by a Unit, part of `FileType`.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum FileFlavor {
    /// Not a special file type.
    Normal,
    /// Like `Normal`, but not directly executable.
    /// For example, a `.wasm` file paired with the "normal" `.js` file.
    Auxiliary,
    /// Something you can link against (e.g., a library).
    Linkable,
    /// An `.rmeta` Rust metadata file.
    Rmeta,
    /// Piece of external debug information (e.g., `.dSYM`/`.pdb` file).
    DebugInfo,
    /// SBOM (Software Bill of Materials pre-cursor) file (e.g. cargo-sbon.json).
    Sbom,
    /// Unremap file for `trim-paths` (e.g. `foo.trim-paths.json`).
    Unremap,
    /// Cross-crate info JSON files generated by rustdoc.
    DocParts,
}

/// Type of each file generated by a Unit.
#[derive(Debug)]
pub struct FileType {
    /// The kind of file.
    pub flavor: FileFlavor,
    /// The crate-type that generates this file.
    ///
    /// `None` for things that aren't associated with a specific crate type,
    /// for example `rmeta` files.
    pub crate_type: Option<CrateType>,
    /// The suffix for the file (for example, `.rlib`).
    /// This is an empty string for executables on Unix-like platforms.
    suffix: String,
    /// The prefix for the file (for example, `lib`).
    /// This is an empty string for things like executables.
    prefix: String,
    /// Flag to convert hyphen to underscore when uplifting.
    should_replace_hyphens: bool,
}

impl FileType {
    /// The filename for this `FileType` created by rustc.
    pub fn output_filename(&self, target: &Target, metadata: Option<&str>) -> String {
        match metadata {
            Some(metadata) => format!(
                "{}{}-{}{}",
                self.prefix,
                target.crate_name(),
                metadata,
                self.suffix
            ),
            None => format!("{}{}{}", self.prefix, target.crate_name(), self.suffix),
        }
    }

    /// The filename for this `FileType` that Cargo should use when "uplifting"
    /// it to the destination directory.
    pub fn uplift_filename(&self, target: &Target) -> String {
        let name = match target.binary_filename() {
            Some(name) => name,
            None => {
                // For binary crate type, `should_replace_hyphens` will always be false.
                if self.should_replace_hyphens {
                    target.crate_name()
                } else {
                    target.name().to_string()
                }
            }
        };

        format!("{}{}{}", self.prefix, name, self.suffix)
    }

    /// Creates a new instance representing a `.rmeta` file.
    pub fn new_rmeta() -> FileType {
        // Note that even binaries use the `lib` prefix.
        FileType {
            flavor: FileFlavor::Rmeta,
            crate_type: None,
            suffix: ".rmeta".to_string(),
            prefix: "lib".to_string(),
            should_replace_hyphens: true,
        }
    }

    pub fn output_prefix_suffix(&self, target: &Target) -> (String, String) {
        (
            format!("{}{}-", self.prefix, target.crate_name()),
            self.suffix.clone(),
        )
    }
}

// Trust (DECISION_QUEUE TARGO-PROBE-MIR-1): the MIR-pipeline options a Trust
// proof session refuses by name, in rustc's canonical `_` spelling: the list of
// `rustc_session::trust_mir_pipeline_option_refusal` (T6, `8e7067d334`). A copy:
// when that list grows, a probe that keeps the new option aborts at T6's refusal
// as every probe did before this list existed, loudly, until the copy follows.
const TRUST_PROOF_SESSION_MIR_PIPELINE_OPTIONS: [&str; 9] = [
    "mir_opt_level",
    "inline_mir",
    "inline_mir_threshold",
    "inline_mir_hint_threshold",
    "inline_mir_forwarder_threshold",
    "mir_enable_passes",
    "mir_opt_bisect_limit",
    "mir_preserve_ub",
    "mir_strip_debuginfo",
];

// Trust: target-info probes are `--print` queries over stdin and compile no
// crate. Targo's authenticated Trust policy must remain in `TargetInfo::rustflags`
// for real units and fingerprinting, but passing it to the early-exit probe is
// both meaningless and rejected by trustc.  Rustc accepts `-`/`_` aliases, so
// classify through the same canonical option parser rather than matching one
// spelling.
//
// Trust (DECISION_QUEUE TARGO-PROBE-MIR-1): the probe also drops the
// MIR-pipeline options above. With every `-Ztrust_*` option gone the probe runs
// at the compiler's default, which on a trustc that verifies by default is a
// proof session, and T6 refuses those options there: `targo --unverified build`
// with `-Zinline-mir` in its flags aborted at the probe although every unit of
// that lane accepts it. (That lane's probe keeps its off-switch since
// TARGO-PROBE-LANE-1, below; its default `trust_verify` query, which runs at the
// default, drops these options too.) No MIR option changes anything the probe
// reports (file names, sysroot, split-debuginfo, crate name, cfg), and every
// unit keeps the options, so a verified run that carries one is still refused,
// at its first unit.
//
// Only `-Z` options are classified, joined (`-Zname`) or split (`-Z name`). An
// operand of another option is never read as an option (TARGO-PROBE-OPERAND-1:
// the `trust_x` of `--cfg trust_x` used to be dropped, and the `--cfg` left
// behind took the probe's next argument).
//
// Trust (DECISION_QUEUE TARGO-PROBE-LANE-1): in the explicitly unverified lane
// the probe then gets the lane's off-switch back, last, so it answers as that
// lane's units compile (`TargetInfoProbeLane`). Every other lane's probe argv
// is what this function returned before that ruling.
fn target_info_probe_flags(flags: &[String], lane: TargetInfoProbeLane) -> Vec<String> {
    let mut out = without_z_options(flags, |name| {
        name.starts_with("trust_") || TRUST_PROOF_SESSION_MIR_PIPELINE_OPTIONS.contains(&name)
    });
    if lane.keeps_off_switch(flags) {
        out.push(format!("-Z{}", crate::compiler::TRUST_VERIFY_OFF_OPTION));
    }
    out
}

/// `flags` minus every `-Z` option, joined (`-Zname`) or split (`-Z name`),
/// whose canonical name `dropped` selects. A split `-Z` and its operand are
/// one option, kept or dropped together; no other token is classified.
fn without_z_options(flags: &[String], dropped: impl Fn(&str) -> bool) -> Vec<String> {
    let is_dropped = |option: &str| dropped(&rustc_option_parts(option.trim_start()).0);
    let mut out = Vec::with_capacity(flags.len());
    let mut i = 0;
    while i < flags.len() {
        if flags[i] == "-Z" {
            let width = if i + 1 < flags.len() { 2 } else { 1 };
            if !flags.get(i + 1).is_some_and(|option| is_dropped(option)) {
                out.extend(flags[i..i + width].iter().cloned());
            }
            i += width;
            continue;
        }
        if !flags[i]
            .strip_prefix("-Z")
            .is_some_and(|option| is_dropped(option))
        {
            out.push(flags[i].clone());
        }
        i += 1;
    }
    out
}

// Trust (DECISION_QUEUE TARGO-PROBE-LANE-1): which compile a target-info probe
// answers for.
//
// Every unit of the explicitly unverified lane (`targo --unverified`, and
// `targo tippy`, which runs it) compiles with the lane's `-Ztrust-verify=off`.
// A probe stripped of it answered at the compiler's default instead, which on
// a trustc that verifies by default is a verifying compile: it refused
// `-Zcontract-checks` the units accept (the build exited 101 at the probe), and
// it reported `debug_assertions`, `overflow_checks` and `ub_checks`, forced on
// by verification, for units that have none of them (`-Copt-level=3`), so build
// scripts saw `CARGO_CFG_OVERFLOW_CHECKS` and `cfg(overflow_checks)` tables were
// selected for a binary that wraps on overflow. That lane's probe now keeps the
// off-switch, and `trust_verify` alone is taken from the compiler's default (one
// more `--print=cfg` query, `trust_verify_default_query_process`), so a
// `[target.'cfg(trust_verify)']` table still reaches `targo --unverified` and
// `targo tippy` alike (T14-TIPPY-1).
//
// The verified lane's units verify, so the default is their answer: its probe,
// and ordinary Cargo's, are unchanged, and neither runs the second query. So is
// the probe of a `targo trust` selection probe that runs in the unverified lane
// (the trust-cg unit-graph preflight): it stands in for the verified build, and
// must select the `[target.'cfg(..)']` tables and dependencies that build's
// probe selects (`TargetInfoProbeLane::of`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum TargetInfoProbeLane {
    /// Verified Targo, ordinary Cargo, and `targo trust`'s selection probes:
    /// the probe drops every Trust option.
    CompilerDefault,
    /// The explicitly unverified lane: the probe keeps the lane's off-switch.
    ExplicitlyUnverified,
}

impl TargetInfoProbeLane {
    /// The probe lane of `lane`, the lane `extra_args` resolves the Rust flags
    /// in, so the two cannot disagree. `ExplicitlyUnverified` where
    /// `extra_args` appends the off-switch for the lane's own units
    /// (`lane.no_verify_fast`, which a verified lane never has), unless the
    /// lane was handed `TRUST_TARGO_LANE_RUSTFLAGS`: outside the verified lane
    /// only `targo trust`'s selection probes carry one
    /// (`refuse_options_outside_the_probe_lane`), and of those only the trust-cg
    /// unit-graph preflight runs in the unverified lane; it resolves the graph
    /// of the verified build it guards, whose probe answers at the default, so
    /// its probe answers there too, as before TARGO-PROBE-LANE-1.
    fn of(lane: &TrustLane) -> TargetInfoProbeLane {
        if lane.no_verify_fast && !lane.verified && lane.rustflags.is_none() {
            TargetInfoProbeLane::ExplicitlyUnverified
        } else {
            TargetInfoProbeLane::CompilerDefault
        }
    }

    /// Whether the probe of `flags` (the resolved rustflags) keeps the lane's
    /// off-switch: in the explicitly unverified lane, when `flags` turn
    /// verification off, which that lane's final `-Ztrust-verify=off` makes
    /// them do. Exactly then the probe runs the default `trust_verify` query.
    fn keeps_off_switch(self, flags: &[String]) -> bool {
        self == TargetInfoProbeLane::ExplicitlyUnverified
            && effective_trust_verification_is_enabled(flags) == Some(false)
    }
}

// Trust (DECISION_QUEUE TARGO-PROBE-LANE-1): the options other than the Trust
// family that a Trust compilation refuses, in rustc's canonical `_` spelling,
// beside the MIR-pipeline list above: `rustc_driver_impl::trust_option_domain_error`
// refuses `-Zcontract-checks` and `-Zlink-only` whenever Trust semantics are
// active. A copy, as the list above is: if the compiler's list grows, the
// default query of a lane whose flags carry the new option fails loudly, as
// every probe of that lane did before this ruling, until the copy follows.
const TRUST_COMPILATION_REFUSED_OPTIONS: [&str; 2] = ["contract_checks", "link_only"];

/// The flags of the default `trust_verify` query: the resolved rustflags minus
/// the Trust family (`-Ztrust-*`, `-Zno-trust-*`) and every option a Trust
/// compilation refuses, so the query answers at the compiler's default.
fn trust_verify_default_query_flags(flags: &[String]) -> Vec<String> {
    without_z_options(flags, |name| {
        name.starts_with("trust_")
            || name.starts_with("no_trust_")
            || TRUST_PROOF_SESSION_MIR_PIPELINE_OPTIONS.contains(&name)
            || TRUST_COMPILATION_REFUSED_OPTIONS.contains(&name)
    })
}

/// The explicitly unverified lane's second query: `--print=cfg` at the
/// compiler's default, of which only the `trust_verify` line is read
/// (`reports_trust_verify`). It runs as the probe runs (same program, wrapper
/// rule and Cargo `[env]`, no `RUSTC_LOG`), and the caller runs it through
/// `Rustc::cached_output` like every probe. Only that lane runs it, where the
/// verified-Targo target-path rule does not apply.
fn trust_verify_default_query_process(
    gctx: &GlobalContext,
    rustc: &Rustc,
    kind: CompileKind,
    flags: &[String],
    branded: bool,
) -> CargoResult<ProcessBuilder> {
    let mut process = target_info_probe_process(rustc, branded);
    apply_env_config(gctx, &mut process)?;
    process
        .arg("-")
        .arg("--crate-name")
        .arg("___")
        .arg("--print=cfg")
        .args(&trust_verify_default_query_flags(flags))
        .env_remove("RUSTC_LOG");
    kind.add_target_arg(&mut process);
    Ok(process)
}

/// Whether the default query's `--print=cfg` output lists `trust_verify`.
fn reports_trust_verify(output: &str) -> bool {
    output.lines().any(|line| line == "trust_verify")
}

/// Adds `trust_verify` to a probe's cfg set, where rustc's sorted `--print=cfg`
/// would have listed it, unless the set has it already.
fn add_trust_verify_cfg(cfg: &mut Vec<Cfg>) -> CargoResult<()> {
    let trust_verify = Cfg::from_str("trust_verify")?;
    if !cfg.contains(&trust_verify) {
        let name = trust_verify.to_string();
        let at = cfg
            .iter()
            .position(|other| other.to_string() > name)
            .unwrap_or(cfg.len());
        cfg.insert(at, trust_verify);
    }
    Ok(())
}

// Trust (T14b, DECISION_QUEUE T14-TIPPY-1): in a branded invocation the
// target-info probes run the selected compiler itself, never through
// `RUSTC_WORKSPACE_WRAPPER`. The probe already strips the lane's Trust tokens so
// its answer does not depend on the lane; skipping the workspace wrapper makes
// it independent of the wrapper too. The one answer a wrapper changed was
// `trust_verify`: tippy-driver runs every compile, this probe included, through
// the evidence-inert route, which turns verification off, so `targo tippy`
// never matched a `[target.'cfg(trust_verify)']` table and resolved other
// platform dependencies and `CARGO_CFG_*` than `targo --unverified check`.
// Ordinary Cargo keeps upstream's probe through the wrapper. (Since
// TARGO-PROBE-LANE-1 the explicitly unverified lane's probe keeps that lane's
// off-switch, and its `trust_verify` comes from a second query at the
// compiler's default, which runs on the same program: `TargetInfoProbeLane`.)
fn target_info_probe_process(rustc: &Rustc, branded: bool) -> ProcessBuilder {
    if branded {
        rustc.process()
    } else {
        rustc.workspace_process()
    }
}

impl TargetInfo {
    /// Learns the information of target platform from `rustc` invocation(s).
    ///
    /// Generally, the first time calling this function is expensive, as it may
    /// query `rustc` several times. To reduce the cost, output of each `rustc`
    /// invocation is cached by [`Rustc::cached_output`].
    ///
    /// Search `Tricky` to learn why querying `rustc` several times is needed.
    #[tracing::instrument(skip_all)]
    pub fn new(
        gctx: &GlobalContext,
        requested_kinds: &[CompileKind],
        rustc: &Rustc,
        kind: CompileKind,
    ) -> CargoResult<TargetInfo> {
        validate_verified_targo_target_origin(rustc, kind)?;
        // Trust (DECISION_QUEUE TARGO-PROBE-LANE-1): the lane of the Rust flags
        // is resolved once and passed in, so the probe's lane is derived from
        // the lane `extra_args` resolves the flags in (`TargetInfoProbeLane::of`),
        // and a test can drive the probes in every lane (the lane markers and
        // the frontend brand are process-wide).
        let lane = TrustLane::current(gctx, Flags::Rust)?;
        TargetInfo::new_in_lane(
            gctx,
            requested_kinds,
            rustc,
            kind,
            &lane,
            crate::is_targo_invocation(),
        )
    }

    /// `new` with the Rust flags' lane and the frontend brand passed in.
    fn new_in_lane(
        gctx: &GlobalContext,
        requested_kinds: &[CompileKind],
        rustc: &Rustc,
        kind: CompileKind,
        lane: &TrustLane,
        branded: bool,
    ) -> CargoResult<TargetInfo> {
        let mut rustflags = extra_args_for_lane(
            gctx,
            requested_kinds,
            &rustc.host,
            None,
            kind,
            Flags::Rust,
            lane,
        )?;
        // Trust: the target-info probes below are `--print` queries (crate name
        // `___`, source from stdin) used to discover target cfgs, sysroot, and
        // file-name conventions — they compile nothing. Targo-trust injects
        // `-Ztrust-verify-session=<nonce>` (plus the rest of the trust-verify
        // directive family) into RUSTFLAGS to authenticate verification of the
        // *real* crate compilations. Trustc deliberately refuses to combine a
        // verification session with any `--print` early-exit (that would let a
        // query masquerade as coverage), so passing those directives to a probe
        // aborts the whole build before any crate is verified. Strip the
        // trust-verify family from the probe argv ONLY: it does not affect
        // target cfg/sysroot/file-name discovery, and a probe emits no
        // per-function transport rows, so it cannot launder coverage. The full
        // `rustflags` (including the session nonce) is retained for real crate
        // builds and for fingerprinting, so verification still runs and each
        // session still forces a fresh build. The compiler's defense-in-depth
        // stays in force for every other caller.
        //
        // Trust (DECISION_QUEUE TARGO-PROBE-LANE-1): the explicitly unverified
        // lane's probe keeps that lane's off-switch, and takes `trust_verify`
        // from the compiler's default; see `TargetInfoProbeLane`.
        let probe_lane = TargetInfoProbeLane::of(lane);
        let mut turn = 0;
        loop {
            let extra_fingerprint = kind.fingerprint_hash();

            // Query rustc for several kinds of info from each line of output:
            // 0) file-names (to determine output file prefix/suffix for given crate type)
            // 1) sysroot
            // 2) split-debuginfo
            // 3) cfg
            //
            // Search `--print` to see what we query so far.
            let mut process = target_info_probe_process(rustc, branded);
            apply_env_config(gctx, &mut process)?;
            rustc.configure_verified_loader_environment(&mut process)?;
            if super::super::verified_targo_protocol_active() {
                // Trust: named custom targets are rejected above. Explicit JSON
                // targets carry their own byte binding and never consult this
                // ambient search path, so retaining it can only reopen an
                // untracked input.
                process.env_remove(RUST_TARGET_PATH_ENV);
            }
            process
                .arg("-")
                .arg("--crate-name")
                .arg("___")
                .arg("--print=file-names")
                .args(&target_info_probe_flags(&rustflags, probe_lane))
                .env_remove("RUSTC_LOG");

            // Removes `FD_CLOEXEC` set by `jobserver::Client` to pass jobserver
            // as environment variables specify.
            if let Some(client) = gctx.jobserver_from_env()? {
                process.inherit_jobserver(client);
            }

            kind.add_target_arg(&mut process);

            let crate_type_process = process.clone();
            const KNOWN_CRATE_TYPES: &[CrateType] = &[
                CrateType::Bin,
                CrateType::Rlib,
                CrateType::Dylib,
                CrateType::Cdylib,
                CrateType::Staticlib,
                CrateType::ProcMacro,
            ];
            for crate_type in KNOWN_CRATE_TYPES.iter() {
                process.arg("--crate-type").arg(crate_type.as_str());
            }

            process.arg("--print=sysroot");
            process.arg("--print=split-debuginfo");
            process.arg("--print=crate-name"); // `___` as a delimiter.
            process.arg("--print=cfg");

            // parse_crate_type() relies on "unsupported/unknown crate type" error message,
            // so make warnings always emitted as warnings.
            process.arg("-Wwarnings");

            let (output, error) = rustc
                .cached_output(&process, extra_fingerprint)
                .with_context(
                    || "failed to run `rustc` to learn about target-specific information",
                )?;

            // Trust: Unix filenames may end in CR. Lines would normalize that
            // byte into another sysroot or output name before we could check it.
            #[cfg(not(windows))]
            if output.contains('\r') {
                anyhow::bail!(
                    "rustc target-information output contains an unsupported carriage return"
                );
            }
            let mut lines = output.lines();
            let mut map = HashMap::default();
            for crate_type in KNOWN_CRATE_TYPES {
                let out = parse_crate_type(crate_type, &process, &output, &error, &mut lines)?;
                map.insert(crate_type.clone(), out);
            }

            let Some(line) = lines.next() else {
                return error_missing_print_output("sysroot", &process, &output, &error);
            };
            let sysroot = PathBuf::from(line);
            let sysroot_target_libdir = {
                let mut libdir = sysroot.clone();
                libdir.push("lib");
                libdir.push("rustlib");
                libdir.push(match &kind {
                    CompileKind::Host => rustc.host.as_str(),
                    CompileKind::Target(target) => target.short_name(),
                });
                libdir.push("lib");
                libdir
            };

            let support_split_debuginfo = {
                // HACK: abuse `--print=crate-name` to use `___` as a delimiter.
                let mut res = Vec::new();
                loop {
                    match lines.next() {
                        Some(line) if line == "___" => break,
                        Some(line) => res.push(line.into()),
                        None => {
                            return error_missing_print_output(
                                "split-debuginfo",
                                &process,
                                &output,
                                &error,
                            );
                        }
                    }
                }
                res
            };

            let mut cfg = lines
                .map(|line| Ok(Cfg::from_str(line)?))
                .filter(TargetInfo::not_user_specific_cfg)
                .collect::<CargoResult<Vec<_>>>()
                .with_context(|| {
                    format!(
                        "failed to parse the cfg from `rustc --print=cfg`, got:\n{}",
                        output
                    )
                })?;

            // Trust (DECISION_QUEUE TARGO-PROBE-LANE-1): the explicitly
            // unverified lane's probe answered with the lane's off-switch, so
            // `trust_verify` comes from the compiler's default (T14-TIPPY-1),
            // before the cfg selects any `[target.'cfg(..)']` table below.
            if probe_lane.keeps_off_switch(&rustflags) {
                let mut query =
                    trust_verify_default_query_process(gctx, rustc, kind, &rustflags, branded)?;
                if let Some(client) = gctx.jobserver_from_env()? {
                    query.inherit_jobserver(client);
                }
                let (default_cfg, _) = rustc
                    .cached_output(&query, extra_fingerprint)
                    .with_context(|| {
                        "failed to run `rustc` to learn whether it verifies by default \
                         (`cfg(trust_verify)`)"
                    })?;
                if reports_trust_verify(&default_cfg) {
                    add_trust_verify_cfg(&mut cfg)?;
                }
            }

            // recalculate `rustflags` from above now that we have `cfg`
            // information
            let new_flags = extra_args_for_lane(
                gctx,
                requested_kinds,
                &rustc.host,
                Some(&cfg),
                kind,
                Flags::Rust,
                lane,
            )?;

            // Tricky: `RUSTFLAGS` defines the set of active `cfg` flags, active
            // `cfg` flags define which `.cargo/config` sections apply, and they
            // in turn can affect `RUSTFLAGS`! This is a bona fide mutual
            // dependency, and it can even diverge (see `cfg_paradox` test).
            //
            // So what we do here is running at most *two* iterations of
            // fixed-point iteration, which should be enough to cover
            // practically useful cases, and warn if that's not enough for
            // convergence.
            let reached_fixed_point = new_flags == rustflags;
            if !reached_fixed_point && turn == 0 {
                turn += 1;
                rustflags = new_flags;
                continue;
            }
            if !reached_fixed_point {
                gctx.shell().warn("non-trivial mutual dependency between target-specific configuration and RUSTFLAGS")?;
            }

            let mut supports_std: Option<bool> = None;

            // The '--print=target-spec-json' is an unstable option of rustc, therefore only
            // try to fetch this information if rustc allows nightly features. Additionally,
            // to avoid making two rustc queries when not required, only try to fetch the
            // target-spec when the '-Zbuild-std' option is passed.
            if gctx.cli_unstable().build_std.is_some() {
                let mut target_spec_process = target_info_probe_process(rustc, branded);
                apply_env_config(gctx, &mut target_spec_process)?;
                rustc.configure_verified_loader_environment(&mut target_spec_process)?;
                // Trust: same closed target origin as the probe above — a
                // `-Zbuild-std` spec query must resolve the same target the
                // real units will.
                if super::super::verified_targo_protocol_active() {
                    target_spec_process.env_remove(RUST_TARGET_PATH_ENV);
                }
                target_spec_process
                    .arg("--print=target-spec-json")
                    .arg("-Zunstable-options")
                    .args(&target_info_probe_flags(&rustflags, probe_lane))
                    .env_remove("RUSTC_LOG");

                kind.add_target_arg(&mut target_spec_process);

                #[derive(Deserialize)]
                struct Metadata {
                    pub std: Option<bool>,
                }

                #[derive(Deserialize)]
                struct TargetSpec {
                    pub metadata: Metadata,
                }

                if let Ok(output) = crate::context::compiler_query::output(&target_spec_process) {
                    if let Ok(spec) = serde_json::from_slice::<TargetSpec>(&output.stdout) {
                        supports_std = spec.metadata.std;
                    }
                }
            }

            let should_embed_metadata = match gctx.cli_unstable().embed_metadata {
                Some(v) => v,
                None => {
                    let cargo_nightly = matches!(
                        crate::version().release_channel.as_deref(),
                        Some("nightly" | "dev")
                    );
                    let rustc_nightly = matches!(rustc.version.pre.as_str(), "dev" | "nightly");

                    // Enable -Zembed-metadata=no by default if both cargo and rustc are nightly
                    let is_nightly = cargo_nightly && rustc_nightly;
                    !is_nightly
                }
            };

            return Ok(TargetInfo {
                crate_type_process,
                crate_types: RefCell::new(map),
                sysroot,
                sysroot_target_libdir,
                rustflags: rustflags.into(),
                rustdocflags: extra_args(
                    gctx,
                    requested_kinds,
                    &rustc.host,
                    Some(&cfg),
                    kind,
                    Flags::Rustdoc,
                )?
                .into(),
                cfg,
                supports_std,
                support_split_debuginfo,
                should_embed_metadata,
            });
        }
    }

    pub(super) fn not_user_specific_cfg(cfg: &CargoResult<Cfg>) -> bool {
        if let Ok(Cfg::Name(cfg_name)) = cfg {
            // This should also include "debug_assertions", but it causes
            // regressions. Maybe some day in the distant future it can be
            // added (and possibly change the warning to an error).
            if cfg_name == "proc_macro" {
                return false;
            }
        }
        true
    }

    /// All the target [`Cfg`] settings.
    pub fn cfg(&self) -> &[Cfg] {
        &self.cfg
    }

    /// Returns the list of file types generated by the given crate type.
    ///
    /// Returns `None` if the target does not support the given crate type.
    fn file_types(
        &self,
        crate_type: &CrateType,
        flavor: FileFlavor,
        target_tuple: &str,
    ) -> CargoResult<Option<Vec<FileType>>> {
        let crate_type = if *crate_type == CrateType::Lib {
            CrateType::Rlib
        } else {
            crate_type.clone()
        };

        let mut crate_types = self.crate_types.borrow_mut();
        let entry = crate_types.entry(crate_type.clone());
        let crate_type_info = match entry {
            Entry::Occupied(o) => &*o.into_mut(),
            Entry::Vacant(v) => {
                let value = self.discover_crate_type(v.key())?;
                &*v.insert(value)
            }
        };
        let Some((prefix, suffix)) = crate_type_info else {
            return Ok(None);
        };
        let mut ret = vec![FileType {
            suffix: suffix.clone(),
            prefix: prefix.clone(),
            flavor,
            crate_type: Some(crate_type.clone()),
            should_replace_hyphens: crate_type != CrateType::Bin,
        }];

        // Window shared library import/export files.
        if crate_type.is_dynamic() {
            // Note: Custom JSON specs can alter the suffix. For now, we'll
            // just ignore non-DLL suffixes.
            if target_tuple.ends_with("-windows-msvc") && suffix == ".dll" {
                // See https://docs.microsoft.com/en-us/cpp/build/reference/working-with-import-libraries-and-export-files
                // for more information about DLL import/export files.
                ret.push(FileType {
                    suffix: ".dll.lib".to_string(),
                    prefix: prefix.clone(),
                    flavor: FileFlavor::Auxiliary,
                    crate_type: Some(crate_type.clone()),
                    should_replace_hyphens: true,
                });
                // NOTE: lld does not produce these
                ret.push(FileType {
                    suffix: ".dll.exp".to_string(),
                    prefix: prefix.clone(),
                    flavor: FileFlavor::Auxiliary,
                    crate_type: Some(crate_type.clone()),
                    should_replace_hyphens: true,
                });
            } else if suffix == ".dll"
                && (target_tuple.ends_with("windows-gnu")
                    || target_tuple.ends_with("windows-gnullvm")
                    || target_tuple.ends_with("cygwin"))
            {
                // See https://cygwin.com/cygwin-ug-net/dll.html for more
                // information about GNU import libraries.
                // LD can link DLL directly, but LLD requires the import library.
                ret.push(FileType {
                    suffix: ".dll.a".to_string(),
                    prefix: "lib".to_string(),
                    flavor: FileFlavor::Auxiliary,
                    crate_type: Some(crate_type.clone()),
                    should_replace_hyphens: true,
                })
            }
        }

        if target_tuple.starts_with("wasm32-") && crate_type == CrateType::Bin && suffix == ".js" {
            // emscripten binaries generate a .js file, which loads a .wasm
            // file.
            ret.push(FileType {
                suffix: ".wasm".to_string(),
                prefix: prefix.clone(),
                flavor: FileFlavor::Auxiliary,
                crate_type: Some(crate_type.clone()),
                // Name `foo-bar` will generate a `foo_bar.js` and
                // `foo_bar.wasm`. Cargo will translate the underscore and
                // copy `foo_bar.js` to `foo-bar.js`. However, the wasm
                // filename is embedded in the .js file with an underscore, so
                // it should not contain hyphens.
                should_replace_hyphens: true,
            });
            // And a map file for debugging. This is only emitted with debug=2
            // (-g4 for emcc).
            ret.push(FileType {
                suffix: ".wasm.map".to_string(),
                prefix: prefix.clone(),
                flavor: FileFlavor::DebugInfo,
                crate_type: Some(crate_type.clone()),
                should_replace_hyphens: true,
            });
        }

        // Handle separate debug files.
        let is_apple = target_tuple.contains("-apple-");
        if matches!(
            crate_type,
            CrateType::Bin | CrateType::Dylib | CrateType::Cdylib | CrateType::ProcMacro
        ) {
            if is_apple {
                let suffix = if crate_type == CrateType::Bin {
                    ".dSYM".to_string()
                } else {
                    ".dylib.dSYM".to_string()
                };
                ret.push(FileType {
                    suffix,
                    prefix: prefix.clone(),
                    flavor: FileFlavor::DebugInfo,
                    crate_type: Some(crate_type),
                    // macOS tools like lldb use all sorts of magic to locate
                    // dSYM files. See https://lldb.llvm.org/use/symbols.html
                    // for some details. It seems like a `.dSYM` located next
                    // to the executable with the same name is one method. The
                    // dSYM should have the same hyphens as the executable for
                    // the names to match.
                    should_replace_hyphens: false,
                })
            } else if target_tuple.ends_with("-msvc") || target_tuple.ends_with("-uefi") {
                ret.push(FileType {
                    suffix: ".pdb".to_string(),
                    prefix: prefix.clone(),
                    flavor: FileFlavor::DebugInfo,
                    crate_type: Some(crate_type),
                    // The absolute path to the pdb file is embedded in the
                    // executable. If the exe/pdb pair is moved to another
                    // machine, then debuggers will look in the same directory
                    // of the exe with the original pdb filename. Since the
                    // original name contains underscores, they need to be
                    // preserved.
                    should_replace_hyphens: true,
                })
            } else {
                // Because DWARF Package (dwp) files are produced after the
                // fact by another tool, there is nothing in the binary that
                // provides a means to locate them. By convention, debuggers
                // take the binary filename and append ".dwp" (including to
                // binaries that already have an extension such as shared libs)
                // to find the dwp.
                ret.push(FileType {
                    // It is important to preserve the existing suffix for
                    // e.g. shared libraries, where the dwp for libfoo.so is
                    // expected to be at libfoo.so.dwp.
                    suffix: format!("{suffix}.dwp"),
                    prefix: prefix.clone(),
                    flavor: FileFlavor::DebugInfo,
                    crate_type: Some(crate_type.clone()),
                    // Likewise, the dwp needs to match the primary artifact's
                    // hyphenation exactly.
                    should_replace_hyphens: crate_type != CrateType::Bin,
                })
            }
        }

        Ok(Some(ret))
    }

    fn discover_crate_type(&self, crate_type: &CrateType) -> CargoResult<Option<(String, String)>> {
        let mut process = self.crate_type_process.clone();

        process.arg("--crate-type").arg(crate_type.as_str());

        let output = crate::context::compiler_query::exec(&process).with_context(|| {
            format!(
                "failed to run `rustc` to learn about crate-type {} information",
                crate_type
            )
        })?;

        let error = str::from_utf8(&output.stderr).unwrap();
        let output = str::from_utf8(&output.stdout).unwrap();
        parse_crate_type(crate_type, &process, output, error, &mut output.lines())
    }

    /// Returns all the file types generated by rustc for the given `mode`/`target_kind`.
    ///
    /// The first value is a Vec of file types generated, the second value is
    /// a list of `CrateTypes` that are not supported by the given target.
    pub fn rustc_outputs(
        &self,
        mode: CompileMode,
        target_kind: &TargetKind,
        target_tuple: &str,
    ) -> CargoResult<(Vec<FileType>, Vec<CrateType>)> {
        match mode {
            CompileMode::Build => self.calc_rustc_outputs(target_kind, target_tuple),
            CompileMode::Test => {
                match self.file_types(&CrateType::Bin, FileFlavor::Normal, target_tuple)? {
                    Some(fts) => Ok((fts, Vec::new())),
                    None => Ok((Vec::new(), vec![CrateType::Bin])),
                }
            }
            CompileMode::Check { .. } => Ok((vec![FileType::new_rmeta()], Vec::new())),
            CompileMode::Doc { .. }
            | CompileMode::Doctest
            | CompileMode::Docscrape
            | CompileMode::RunCustomBuild => {
                panic!("asked for rustc output for non-rustc mode")
            }
        }
    }

    fn calc_rustc_outputs(
        &self,
        target_kind: &TargetKind,
        target_tuple: &str,
    ) -> CargoResult<(Vec<FileType>, Vec<CrateType>)> {
        let mut unsupported = Vec::new();
        let mut result = Vec::new();
        let crate_types = target_kind.rustc_crate_types();
        for crate_type in &crate_types {
            let flavor = if crate_type.is_linkable() {
                FileFlavor::Linkable
            } else {
                FileFlavor::Normal
            };
            let file_types = self.file_types(crate_type, flavor, target_tuple)?;
            match file_types {
                Some(types) => {
                    result.extend(types);
                }
                None => {
                    unsupported.push(crate_type.clone());
                }
            }
        }
        if !result.is_empty() {
            if !self.should_embed_metadata()
                && crate_types
                    .iter()
                    .any(|ct| ct.benefits_from_no_embed_metadata())
            {
                // Add .rmeta when we apply -Zembed-metadata=no to the unit.
                result.push(FileType::new_rmeta());
            } else if !crate_types.iter().any(|ct| ct.requires_upstream_objects()) {
                // Only add rmeta if pipelining
                result.push(FileType::new_rmeta());
            }
        }
        Ok((result, unsupported))
    }

    /// Checks if the debuginfo-split value is supported by this target
    pub fn supports_debuginfo_split(&self, split: InternedString) -> bool {
        self.support_split_debuginfo
            .iter()
            .any(|sup| sup.as_str() == split.as_str())
    }

    /// Checks if a target maybe support std.
    ///
    /// If no explicitly stated in target spec json, we treat it as "maybe support".
    ///
    /// This is only useful for `-Zbuild-std` to determine the default set of
    /// crates it is going to build.
    pub fn maybe_support_std(&self) -> bool {
        matches!(self.supports_std, Some(true) | None)
    }

    /// Should crate metadata be embedded into .rlib files?
    /// If not, they will only be stored in .rmeta files.
    pub fn should_embed_metadata(&self) -> bool {
        self.should_embed_metadata
    }
}

/// Takes rustc output (using specialized command line args), and calculates the file prefix and
/// suffix for the given crate type, or returns `None` if the type is not supported. (e.g., for a
/// Rust library like `libcargo.rlib`, we have prefix "lib" and suffix "rlib").
///
/// The caller needs to ensure that the lines object is at the correct line for the given crate
/// type: this is not checked.
///
/// This function can not handle more than one file per type (with wasm32-unknown-emscripten, there
/// are two files for bin (`.wasm` and `.js`)).
fn parse_crate_type(
    crate_type: &CrateType,
    cmd: &ProcessBuilder,
    output: &str,
    error: &str,
    lines: &mut str::Lines<'_>,
) -> CargoResult<Option<(String, String)>> {
    let not_supported = error.lines().any(|line| {
        (line.contains("unsupported crate type") || line.contains("unknown crate type"))
            && line.contains(&format!("crate type `{}`", crate_type))
    });
    if not_supported {
        return Ok(None);
    }
    let Some(line) = lines.next() else {
        anyhow::bail!(
            "malformed output when learning about crate-type {} information\n{}",
            crate_type,
            output_err_info(cmd, output, error)
        )
    };
    // Trust: rustc prints the basename verbatim, without presentation padding.
    // Whitespace belongs to the target's filename prefix/suffix.
    let Some(marker) = line.find("___") else {
        return error_missing_print_output("file-names", cmd, output, error);
    };
    // Trust: prefix/suffix underscores can overlap the probe's crate name.
    // One observed name cannot disambiguate multiple possible marker positions.
    if line[marker + 1..].contains("___") {
        anyhow::bail!(
            "ambiguous output of --print=file-names for crate type {crate_type}: \
             the crate-name marker has multiple positions"
        );
    }
    let prefix = &line[..marker];
    let suffix = &line[marker + 3..];

    Ok(Some((prefix.to_string(), suffix.to_string())))
}

/// Helper for creating an error message for missing output from a certain `--print` request.
fn error_missing_print_output<T>(
    request: &str,
    cmd: &ProcessBuilder,
    stdout: &str,
    stderr: &str,
) -> CargoResult<T> {
    let err_info = output_err_info(cmd, stdout, stderr);
    anyhow::bail!(
        "output of --print={request} missing when learning about \
     target-specific information from rustc\n{err_info}",
    )
}

/// Helper for creating an error message when parsing rustc output fails.
fn output_err_info(cmd: &ProcessBuilder, stdout: &str, stderr: &str) -> String {
    let mut result = format!("command was: {}\n", cmd);
    if !stdout.is_empty() {
        result.push_str("\n--- stdout\n");
        result.push_str(stdout);
    }
    if !stderr.is_empty() {
        result.push_str("\n--- stderr\n");
        result.push_str(stderr);
    }
    if stdout.is_empty() && stderr.is_empty() {
        result.push_str("(no output received)");
    }
    result
}

/// Compiler flags for either rustc or rustdoc.
#[derive(Debug, Copy, Clone)]
pub(super) enum Flags {
    Rust,
    Rustdoc,
}

impl Flags {
    fn as_key(self) -> &'static str {
        match self {
            Flags::Rust => "rustflags",
            Flags::Rustdoc => "rustdocflags",
        }
    }

    fn as_env(self) -> &'static str {
        match self {
            Flags::Rust => "RUSTFLAGS",
            Flags::Rustdoc => "RUSTDOCFLAGS",
        }
    }
}

/// Acquire extra flags to pass to the compiler from various locations.
///
/// The locations are:
///
///  - the `CARGO_ENCODED_RUSTFLAGS` environment variable
///  - the `RUSTFLAGS` environment variable
///
/// then if none of those were found
///
///  - `target.*.rustflags` from the config (.cargo/config)
///  - `target.cfg(..).rustflags` from the config
///  - `host.*.rustflags` from the config if compiling a host artifact or without `--target`
///     (requires `-Zhost-config`)
///
/// then if none of those were found
///
///  - `build.rustflags` from the config
///
/// The behavior differs slightly when cross-compiling (or, specifically, when `--target` is
/// provided) for artifacts that are always built for the host (plugins, build scripts, ...).
/// For those artifacts, _only_ `host.*.rustflags` is respected, and no other configuration
/// sources, _regardless of the value of `target-applies-to-host`_. This is counterintuitive, but
/// necessary to retain backwards compatibility with older versions of Cargo.
///
/// Rules above also applies to rustdoc. Just the key would be `rustdocflags`/`RUSTDOCFLAGS`.
fn extra_args(
    gctx: &GlobalContext,
    requested_kinds: &[CompileKind],
    host_triple: &str,
    target_cfg: Option<&[Cfg]>,
    kind: CompileKind,
    flags: Flags,
) -> CargoResult<Vec<String>> {
    let lane = TrustLane::current(gctx, flags)?;
    extra_args_for_lane(
        gctx,
        requested_kinds,
        host_triple,
        target_cfg,
        kind,
        flags,
        &lane,
    )
}

// Trust: `extra_args` in a lane the caller resolved (`TargetInfo::new_in_lane`),
// with its notices noted.
fn extra_args_for_lane(
    gctx: &GlobalContext,
    requested_kinds: &[CompileKind],
    host_triple: &str,
    target_cfg: Option<&[Cfg]>,
    kind: CompileKind,
    flags: Flags,
    lane: &TrustLane,
) -> CargoResult<Vec<String>> {
    let (args, notices) = extra_args_in_lane(
        gctx,
        requested_kinds,
        host_triple,
        target_cfg,
        kind,
        flags,
        lane,
    )?;
    for notice in notices {
        note_lane_notice_once(gctx, notice)?;
    }
    Ok(args)
}

// Trust: `extra_args` with the lane state passed in, so a test can drive every
// branch over a real `GlobalContext` and its configuration (the frontend brand
// and the verified marker are process-wide). Returns the resolved flags and
// one notice per project option the lane owns and dropped (T14-APPEND-2).
fn extra_args_in_lane(
    gctx: &GlobalContext,
    requested_kinds: &[CompileKind],
    host_triple: &str,
    target_cfg: Option<&[Cfg]>,
    kind: CompileKind,
    flags: Flags,
    lane: &TrustLane,
) -> CargoResult<(Vec<String>, Vec<String>)> {
    let mut notices = Vec::new();
    // Trust: keep the unified `args` structure (no early return) so the
    // fast-lint flag below appends to the RESOLVED flags for every branch;
    // the host-only-config decision itself uses upstream 1.99's extracted
    // `host_artifact_uses_only_host_config` helper (same semantics as the
    // former inline check, shared with upstream's other call site).
    // All other artifacts pick up the RUSTFLAGS, [target.*], and [build], in that order.
    let host_isolated = host_artifact_uses_only_host_config(gctx, requested_kinds, kind)?;
    let mut args = if host_isolated {
        // Host artifacts just get flags from [host], regardless of --target (they
        // don't pick up `RUSTFLAGS` etc.).
        let host = rustflags_from_host_source(gctx, flags, host_triple)?;
        // Trust: Cargo intentionally isolates explicit-target host artifacts
        // (build scripts and proc macros) from RUSTFLAGS. Verified Targo is the
        // one exception: every compiler unit participating in a proof must
        // receive the same verifier policy and session, so the lane's closed
        // verifier protocol crosses the boundary (`TrustLane::host_flags`).
        // Ordinary Cargo never reads the lane.
        match &lane.rustflags {
            Some(_) => lane.host_flags(host, &mut notices)?,
            None => host.map(|host| host.flags).unwrap_or_default(),
        }
    } else if let Some(environment) = rustflags_from_env_source(gctx, flags) {
        match &lane.rustflags {
            // Trust (T14a): Cargo's precedence holds in every lane: an
            // environment value replaces the configured tables. Its `-Ztrust-*`
            // tokens are dropped (targo trust names them before its banner and
            // refuses an off-switch), the options the lane owns are dropped
            // with a notice, configured requirement assertions are still
            // checked against the lane, and the lane comes last.
            Some(lane_flags) => {
                refuse_uninspectable_project_flags(&environment)?;
                let environment = FlagSource {
                    origin: environment.origin,
                    flags: without_trust_options(&environment.flags),
                };
                let mut args = drop_lane_owned_options(&environment, lane.ownership, &mut notices);
                if lane.verified {
                    let mut configured =
                        rustflags_from_target_sources(gctx, host_triple, target_cfg, kind, flags)?;
                    if configured.iter().all(|source| source.flags.is_empty()) {
                        configured = rustflags_from_build_source(gctx, flags)?
                            .into_iter()
                            .collect();
                    }
                    configured.retain(|source| !source.flags.is_empty());
                    // Trust (T14a): Cargo's precedence is the rule, but a
                    // committed `--cfg` silently leaving the proof set (an
                    // empty `CARGO_ENCODED_RUSTFLAGS` is enough) is not: name
                    // the variable that won and every table it replaced.
                    if !configured.is_empty() {
                        let replaced = configured
                            .iter()
                            .map(|source| source.origin.as_str())
                            .collect::<Vec<_>>()
                            .join(", ");
                        notices.push(format!(
                            "{} replaces the configured rustflags of {replaced}, as Cargo's \
                             precedence has it: none of them reach this build, and their Trust \
                             requirements are still checked against the lane",
                            environment.origin
                        ));
                        let configured = configured
                            .into_iter()
                            .flat_map(|source| source.flags)
                            .collect::<Vec<_>>();
                        args.extend(reconcile_overridden_config_trust_policy(
                            &configured,
                            lane_flags,
                        )?);
                    }
                }
                args.extend(lane_flags.iter().cloned());
                args
            }
            None => {
                let mut rustflags = environment.flags;
                // Trust: a verified rustdoc invocation (the lane carries Rust
                // flags only). Configuration may still require that policy;
                // dropping those assertions would silently turn a certify,
                // strict-lowering, dependency-including build into another lane.
                if lane.verified {
                    let configured =
                        match rustflags_from_target(gctx, host_triple, target_cfg, kind, flags)? {
                            Some(configured) => Some(configured),
                            None => rustflags_from_build(gctx, flags)?,
                        };
                    if let Some(configured) = configured {
                        let assertions =
                            reconcile_overridden_config_trust_policy(&configured, &rustflags)?;
                        rustflags.extend(assertions);
                    }
                }
                rustflags
            }
        }
    } else {
        let mut configured =
            rustflags_from_target_sources(gctx, host_triple, target_cfg, kind, flags)?;
        if configured.iter().all(|source| source.flags.is_empty()) {
            configured = rustflags_from_build_source(gctx, flags)?
                .into_iter()
                .collect();
        }
        match &lane.rustflags {
            // Trust (T14a): the project's configured flags, minus what the
            // lane owns, then the lane. Configured `-Ztrust-*` tokens stay
            // requirement assertions in the verified lane: each must match the
            // lane or the run is refused, and an off-switch is refused.
            Some(lane_flags) => {
                let mut args = Vec::new();
                for source in &configured {
                    refuse_uninspectable_project_flags(source)?;
                    args.extend(drop_lane_owned_options(
                        source,
                        lane.ownership,
                        &mut notices,
                    ));
                }
                if lane.verified {
                    args = reconcile_lane_trust_policy(&args, &lane.host_policy, "configured")?;
                }
                args.extend(lane_flags.iter().cloned());
                args
            }
            None => configured
                .into_iter()
                .flat_map(|source| source.flags)
                .collect(),
        }
    };

    // Trust: `TargetInfo::new` uses these resolved flags for rustc `--print`
    // probes before compilation units (and their final-argv policy) exist,
    // which makes this the earliest flag boundary that exists at all. Reject the
    // retired Trust exec projection at this first resolved compiler-flags
    // boundary so ambient, target/build config, isolated `[host]`, and rustdoc
    // spellings cannot reach a probe or documentation subprocess.
    if lane.verified {
        reject_retired_contract_checks(&args)?;
    }

    // Trust: the explicitly authorized native unverified path appends
    // `-Ztrust-verify=off` to the rustc flags. Branded Targo refuses to enter
    // this path implicitly. Apply the same tracked
    // off-switch to rustc and rustdoc: `targo doc` is part of the advertised
    // unverified native lane, and leaving rustdoc batteries-on would also expose
    // `cfg(trust_verify)` to documentation builds while ordinary native builds
    // omit it. Appended to
    // the *resolved* flags so config flags are preserved and verified/unverified
    // artifacts never alias.
    //
    // Trust: (2026-10-06) before that, the unverified lane drops every
    // config/env `-Ztrust-*` from the RESOLVED rustdoc flags; see
    // `unverified_lane_rustdoc_flags`. The verified lane is untouched.
    if matches!(flags, Flags::Rustdoc) {
        args = unverified_lane_rustdoc_flags(args, lane.no_verify_fast, lane.verified);
    }
    append_trust_no_verify_fast_flag(&mut args, lane.no_verify_fast);

    Ok((args, notices))
}

// Trust (T14a, DECISION_QUEUE T14-APPEND-1/2): from here to
// `note_lane_notice_once` is Trust-authored. `targo trust` no longer exports
// RUSTFLAGS, which made Cargo ignore every configured table; it hands the
// lane's flags to this process in `TRUST_TARGO_LANE_RUSTFLAGS` instead, and
// `extra_args` appends them to the project's flags, resolved by Cargo's own
// precedence, exactly where the unverified lane appends its off-switch.

/// The lane a branded invocation compiles in, as `extra_args` needs it.
#[derive(Debug, Default)]
struct TrustLane {
    /// The branded frontend accepted `TRUST_TARGO_VERIFY=1`.
    verified: bool,
    /// The explicitly authorized unverified lane (`-Ztrust-verify=off`).
    no_verify_fast: bool,
    /// `TRUST_TARGO_LANE_RUSTFLAGS`, decoded. `Some` only for the Rust flags of
    /// a branded invocation that was handed a lane (possibly empty).
    rustflags: Option<Vec<String>>,
    /// The verified host-policy subset of the lane: what crosses Cargo's
    /// explicit-target host boundary. Empty outside the verified lane.
    host_policy: Vec<String>,
    /// The lane's own `-Zcodegen-backend`, canonicalized.
    codegen_backend: Option<String>,
    /// What the lane sets, so the project's spelling of it is dropped.
    ownership: LaneOwnership,
}

impl TrustLane {
    fn current(gctx: &GlobalContext, flags: Flags) -> CargoResult<TrustLane> {
        let branded = crate::is_targo_invocation();
        let rustflags = if branded && matches!(flags, Flags::Rust) {
            decode_lane_rustflags(gctx.get_env_os(TRUST_TARGO_LANE_RUSTFLAGS_ENV))?
        } else {
            None
        };
        TrustLane::new(
            branded && crate::trust_verified_targo(),
            crate::trust_no_verify_fast(),
            flags,
            rustflags,
        )
    }

    fn new(
        verified: bool,
        no_verify_fast: bool,
        flags: Flags,
        rustflags: Option<Vec<String>>,
    ) -> CargoResult<TrustLane> {
        let Some(lane) = rustflags else {
            if verified && matches!(flags, Flags::Rust) {
                anyhow::bail!(
                    "verified Targo has no lane: `targo trust` hands Cargo its lane in \
                     {TRUST_TARGO_LANE_RUSTFLAGS_ENV}, and nothing else may set TRUST_TARGO_VERIFY=1"
                );
            }
            return Ok(TrustLane {
                verified,
                no_verify_fast,
                ..TrustLane::default()
            });
        };
        refuse_uninspectable_project_flags(&FlagSource {
            origin: format!("`{TRUST_TARGO_LANE_RUSTFLAGS_ENV}`"),
            flags: lane.clone(),
        })?;
        let codegen_backend = verified_targo_target_codegen_backend(&lane)
            .with_context(|| format!("{TRUST_TARGO_LANE_RUSTFLAGS_ENV} is malformed"))?;
        let ownership = LaneOwnership::of(&lane)
            .with_context(|| format!("{TRUST_TARGO_LANE_RUSTFLAGS_ENV} is malformed"))?;
        let host_policy = if verified {
            extract_verified_targo_host_policy(&lane).with_context(|| {
                format!("{TRUST_TARGO_LANE_RUSTFLAGS_ENV} is not a verified lane")
            })?
        } else {
            let options =
                super::super::prefixed_compiler_options(&lane, "-Z").map_err(anyhow::Error::msg)?;
            if let Some((name, _)) = options
                .iter()
                .find(|(name, _)| name.starts_with("trust_") || name.starts_with("no_trust_"))
            {
                anyhow::bail!(
                    "{TRUST_TARGO_LANE_RUSTFLAGS_ENV} carries -Z{name} without TRUST_TARGO_VERIFY=1: \
                     only the verified lane hands Cargo Trust options"
                );
            }
            refuse_options_outside_the_probe_lane(&lane)?;
            Vec::new()
        };
        Ok(TrustLane {
            verified,
            no_verify_fast,
            rustflags: Some(lane),
            host_policy,
            codegen_backend,
            ownership,
        })
    }

    /// `[host]` flags of an explicit-target host artifact under a lane. In the
    /// verified lane they get the lane's host policy (never its codegen
    /// contract, and LLVM when the target compiles through trust-cg, since
    /// build scripts and proc macros need executable and dynamic artifacts
    /// trust-cg does not produce). A probe's unverified lane reaches no host
    /// artifact, but the lane still owns the backend, plugins and LLVM
    /// arguments there, so none loads into its compiler.
    fn host_flags(
        &self,
        host: Option<FlagSource>,
        notices: &mut Vec<String>,
    ) -> CargoResult<Vec<String>> {
        let host = host.unwrap_or_else(|| FlagSource {
            origin: "`[host]`".to_string(),
            flags: Vec::new(),
        });
        refuse_uninspectable_project_flags(&host)?;
        if !self.verified {
            return Ok(drop_lane_owned_options(
                &host,
                LaneOwnership::default(),
                notices,
            ));
        }
        let ownership = LaneOwnership::of(&self.host_policy)?;
        let args = drop_lane_owned_options(&host, ownership, notices);
        // Trust: matching host settings assert the imported policy; they do
        // not create it. Keep the positive verification requirement in the
        // Unit's flags until the resolved graph can discharge it.
        let mut args = reconcile_host_config_trust_policy(&args, &self.host_policy)?;
        if self.codegen_backend.as_deref() == Some("trust-cg") {
            args.extend(["-Z".to_string(), "codegen-backend=llvm".to_string()]);
        }
        args.extend(self.host_policy.iter().cloned());
        Ok(args)
    }
}

/// Outside the verified lane, `targo trust` hands a lane only to its own
/// probes (the metadata, pkgid and config queries and the trust-cg unit-graph
/// preflight), and that lane is trust-cg's codegen contract and the strict
/// safety checks: target cfgs, so the probe resolves the graph the build
/// compiles. Anything else is refused, so the variable is never a second
/// ambient rustflags channel past Cargo's precedence (it is scrubbed from
/// every child, so only a hand-set value can reach here).
fn refuse_options_outside_the_probe_lane(lane: &[String]) -> CargoResult<()> {
    const PROBE_LANE_OPTIONS: &[&str] = &[
        "panic",
        "debuginfo",
        "codegen_units",
        "overflow_checks",
        "debug_assertions",
    ];
    let mut index = 0;
    while index < lane.len() {
        let argument = lane[index].as_str();
        let (option, consumed) = if matches!(argument, "-C" | "--codegen") {
            (lane.get(index + 1).map(String::as_str), 2)
        } else if let Some(option) = argument
            .strip_prefix("--codegen=")
            .or_else(|| argument.strip_prefix("-C").filter(|o| !o.is_empty()))
        {
            (Some(option), 1)
        } else {
            (None, 1)
        };
        let allowed = option
            .is_some_and(|option| PROBE_LANE_OPTIONS.contains(&&*rustc_option_parts(option).0));
        if !allowed {
            anyhow::bail!(
                "{TRUST_TARGO_LANE_RUSTFLAGS_ENV} carries `{argument}` without TRUST_TARGO_VERIFY=1: \
                 outside the verified lane it carries only `targo trust`'s probe contract \
                 (-C panic, debuginfo, codegen-units, overflow-checks, debug-assertions)"
            );
        }
        index += consumed;
    }
    Ok(())
}

/// Decode `TRUST_TARGO_LANE_RUSTFLAGS`, which is always in Cargo's encoded
/// form. An empty value is an empty lane: the lane still owns the backend,
/// plugins and LLVM arguments (the selection probes rely on that).
fn decode_lane_rustflags(value: Option<&OsStr>) -> CargoResult<Option<Vec<String>>> {
    let Some(value) = value else {
        return Ok(None);
    };
    let value = value
        .to_str()
        .ok_or_else(|| anyhow::anyhow!("{TRUST_TARGO_LANE_RUSTFLAGS_ENV} is not valid Unicode"))?;
    Ok(Some(if value.is_empty() {
        Vec::new()
    } else {
        value.split('\x1f').map(str::to_string).collect()
    }))
}

/// What the lane sets beyond the options it always owns, read from the lane
/// itself so the classifier cannot disagree with it.
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
struct LaneOwnership {
    /// `-C overflow-checks` / `-C debug-assertions`: the strict safety checks.
    safety_checks: bool,
    /// `-C panic` / `-C debuginfo` / `-C codegen-units`: trust-cg's codegen
    /// contract (and with it `-C incremental` and `-g`).
    trust_cg_contract: bool,
}

impl LaneOwnership {
    fn of(lane: &[String]) -> CargoResult<LaneOwnership> {
        let mut ownership = LaneOwnership::default();
        for (name, _) in super::super::codegen_compiler_options(lane).map_err(anyhow::Error::msg)? {
            match name.as_str() {
                "overflow_checks" | "debug_assertions" => ownership.safety_checks = true,
                "panic" | "debuginfo" | "codegen_units" => ownership.trust_cg_contract = true,
                _ => {}
            }
        }
        Ok(ownership)
    }
}

/// Why the lane owns a project option (T14-APPEND-2), or `None` when the
/// project keeps it. The backend, LLVM plugins and LLVM arguments are the
/// lane's whenever a lane is present: each can load code into the compiler
/// (an external backend is how the trust-mc engine reaches trustc), and
/// `-Cllvm-args` and `-Zllvm-plugins` accumulate rather than override, so the
/// lane's own spelling coming last would not win.
fn lane_owned_option_reason(
    class: char,
    name: &str,
    ownership: LaneOwnership,
) -> Option<&'static str> {
    match (class, name) {
        ('Z', "codegen_backend") => Some("the lane selects the codegen backend"),
        ('Z', "llvm_plugins") => Some("the lane loads no LLVM plugin into the compiler"),
        ('C', "llvm_args") => Some("the lane passes no LLVM arguments"),
        ('C', "overflow_checks" | "debug_assertions") if ownership.safety_checks => {
            Some("the lane forces the strict safety checks")
        }
        ('C', "panic" | "debuginfo" | "codegen_units" | "incremental")
            if ownership.trust_cg_contract =>
        {
            Some("trust-cg's codegen contract is the lane's")
        }
        _ => None,
    }
}

/// Refuse a project flag whose effect cannot be read off the flag itself: a
/// `@file` argument (rustc expands it into more flags, wherever it sits, so a
/// `-Zcodegen-backend` inside it would load into a target-info probe's or a
/// selection probe's compiler past `drop_lane_owned_options`), and a `--`
/// (after it rustc reads no option, so a lane flag behind it is no flag). The
/// unit's own boundary (`validate_verified_targo_compiler_argument_boundaries`)
/// refuses both too, but the probes run before any unit exists.
fn refuse_uninspectable_project_flags(source: &FlagSource) -> CargoResult<()> {
    if let Some(argfile) = source.flags.iter().find(|flag| flag.starts_with('@')) {
        anyhow::bail!(
            "`{argfile}` from {} is an argument file, whose flags the lane cannot inspect; \
             pass its flags explicitly",
            source.origin
        );
    }
    if source.flags.iter().any(|flag| flag == "--") {
        anyhow::bail!(
            "`--` from {} ends rustc's options, so the lane's own flags could not follow it; \
             remove it",
            source.origin
        );
    }
    Ok(())
}

/// Drop every option the lane owns from one source's flags, keeping the rest
/// in order, and push one notice per dropped option naming its source. `-C`
/// is read in every spelling rustc accepts (`-C x`, `-Cx`, `--codegen x`,
/// `--codegen=x`), and `-g` is `-Cdebuginfo=2`.
fn drop_lane_owned_options(
    source: &FlagSource,
    ownership: LaneOwnership,
    notices: &mut Vec<String>,
) -> Vec<String> {
    let args = &source.flags;
    let mut kept = Vec::with_capacity(args.len());
    let mut index = 0;
    while index < args.len() {
        let argument = args[index].as_str();
        let (class, option, consumed) = if argument == "-Z" {
            ('Z', args.get(index + 1).map(String::as_str), 2)
        } else if matches!(argument, "-C" | "--codegen") {
            ('C', args.get(index + 1).map(String::as_str), 2)
        } else if let Some(option) = argument.strip_prefix("-Z").filter(|o| !o.is_empty()) {
            ('Z', Some(option), 1)
        } else if let Some(option) = argument.strip_prefix("-C").filter(|o| !o.is_empty()) {
            ('C', Some(option), 1)
        } else if let Some(option) = argument.strip_prefix("--codegen=") {
            ('C', Some(option), 1)
        } else {
            ('\0', None, 1)
        };
        let end = (index + consumed).min(args.len());
        let reason = match option {
            Some(option) => {
                lane_owned_option_reason(class, &rustc_option_parts(option).0, ownership)
            }
            None if argument == "-g" && ownership.trust_cg_contract => {
                Some("trust-cg's codegen contract is the lane's")
            }
            None => None,
        };
        match reason {
            Some(reason) => notices.push(format!(
                "`{}` from {} is ignored: {reason}",
                args[index..end].join(" "),
                source.origin
            )),
            None => kept.extend_from_slice(&args[index..end]),
        }
        index = end;
    }
    kept
}

/// Drop every `-Ztrust-*` (and `-Zno-trust-*`) token from environment flags
/// under a lane. targo trust names them before its banner, and refuses an
/// environment off-switch outright, so this drop is never silent.
fn without_trust_options(args: &[String]) -> Vec<String> {
    fn is_trust_option(option: &str) -> bool {
        let name = rustc_option_parts(option).0;
        name.starts_with("trust_") || name.starts_with("no_trust_")
    }
    let mut kept = Vec::with_capacity(args.len());
    let mut index = 0;
    while index < args.len() {
        if args[index] == "-Z" && args.get(index + 1).is_some_and(|o| is_trust_option(o)) {
            index += 2;
            continue;
        }
        if args[index]
            .strip_prefix("-Z")
            .is_some_and(|option| !option.is_empty() && is_trust_option(option))
        {
            index += 1;
            continue;
        }
        kept.push(args[index].clone());
        index += 1;
    }
    kept
}

/// Print each lane notice once per process: `extra_args` runs for every
/// compile kind, twice per target-info fixed point, and again for rustdoc.
fn note_lane_notice_once(gctx: &GlobalContext, notice: String) -> CargoResult<()> {
    static PRINTED: std::sync::Mutex<std::collections::BTreeSet<String>> =
        std::sync::Mutex::new(std::collections::BTreeSet::new());
    let first = PRINTED
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner())
        .insert(notice.clone());
    if first {
        gctx.shell().note(notice)?;
    }
    Ok(())
}

// Trust: the explicitly authorized unverified lane (`targo --unverified doc`,
// `targo --unverified test --doc`) makes no proof claim. trustdoc's embedded
// compiler frontend (`EmbeddedNoOfficialEvidence`,
// `compiler/rustc_driver_impl/src/lib.rs::frontend_forbidden_option` and
// `rustc_interface::interface::apply_no_trust_evidence_typed_policy`) used to
// refuse every `-Ztrust-*` control except the redundant `-Ztrust-verify=off`,
// so a consumer that commits its verified-lane policy to `rustdocflags` or
// `RUSTDOCFLAGS` (ay's certify posture under `[target.'cfg(all())']`) could
// neither document nor run a single doctest in this lane. That frontend now
// decides on the effective configuration and still refuses every evidence
// control a caller sets (DECISION_QUEUE FRONTEND-EFFECTIVE-POSTURE-1); this
// lane hands it none of the caller's Trust options either way. Drop every
// caller-supplied `-Ztrust-*` (both `-Z<opt>` and split `-Z <opt>`, every
// `-`/`_` spelling) from the resolved rustdoc flags. Targo's own
// `-Ztrust-verify=off` is appended afterwards and is KEPT: trustdoc forwards it
// to each doctest compile, which otherwise runs batteries-on under the
// canonical trustc and refuses on the doctest's own obligations — the lane says
// verification is off, and that flag is what makes it so. Only `-Z` tokens are
// classified, so a `--cfg trust_x` operand is never mistaken for an option.
// The authenticated lane (`trust_verified_targo`) and plain Cargo keep their
// flags byte for byte; there the doctest refusal stays the documented gap.
fn unverified_lane_rustdoc_flags(
    args: Vec<String>,
    no_verify_fast: bool,
    verified_targo: bool,
) -> Vec<String> {
    if !no_verify_fast || verified_targo {
        return args;
    }
    fn is_trust_option(option: &str) -> bool {
        rustc_option_parts(option).0.starts_with("trust_")
    }
    let mut out = Vec::with_capacity(args.len());
    let mut index = 0;
    while index < args.len() {
        let arg = &args[index];
        if arg == "-Z" {
            if args
                .get(index + 1)
                .is_some_and(|option| is_trust_option(option))
            {
                index += 2;
                continue;
            }
        } else if arg
            .strip_prefix("-Z")
            .is_some_and(|option| is_trust_option(option))
        {
            index += 1;
            continue;
        }
        out.push(arg.clone());
        index += 1;
    }
    out
}

// Trust: from here to `rustflags_from_env_source` is Trust-authored. It is the
// resolved-flags policy layer — the one place where Cargo has finished merging
// `RUSTFLAGS`, `[target.*]`, `[build]`, and `[host]` but has not yet built any
// Unit, so it is the only point at which the verifier protocol can be settled
// once for probes, units, and fingerprints alike.
//
// Two invariants shape all of it: rustc's option parser takes the *last*
// spelling of an option (so scanning for "any occurrence" is exploitable), and
// `-Z`/`-C` names accept `-`/`_` aliases (so every check goes through
// `rustc_option_parts` rather than matching a literal).
fn reject_retired_contract_checks(rustflags: &[String]) -> CargoResult<()> {
    let mut index = 0;
    while index < rustflags.len() {
        let (option, split) = if rustflags[index] == "-Z" {
            (rustflags.get(index + 1).map(String::as_str), true)
        } else {
            (
                rustflags[index]
                    .strip_prefix("-Z")
                    .filter(|option| !option.is_empty()),
                false,
            )
        };
        if option.is_some_and(|option| rustc_option_parts(option).0 == "contract_checks") {
            anyhow::bail!(
                "resolved compiler flags use retired -Zcontract_checks; certified monitors are selected automatically"
            );
        }
        index += if split { 2 } else { 1 };
    }
    Ok(())
}

fn append_trust_no_verify_fast_flag(args: &mut Vec<String>, enabled: bool) {
    if !enabled {
        return;
    }
    if effective_trust_verification_is_enabled(args) != Some(false) {
        args.push(format!("-Z{}", crate::compiler::TRUST_VERIFY_OFF_OPTION));
    }
}

/// `None` when no occurrence resolves the switch, so a caller that only wrote
/// an unparseable spelling still gets Targo's authoritative final flag.
fn effective_trust_verification_is_enabled(args: &[String]) -> Option<bool> {
    // rustc's option parser keeps the final spelling. Looking for any enabled
    // occurrence would let a later caller-controlled `=false` defeat the
    // native lane while also suppressing Targo's authoritative final flag.
    let mut effective = None;
    let mut index = 0;
    while index < args.len() {
        let (option, consumed) = if args[index] == "-Z" {
            (args.get(index + 1).map(String::as_str), 2)
        } else {
            (
                args[index]
                    .strip_prefix("-Z")
                    .filter(|option| !option.is_empty()),
                1,
            )
        };
        if let Some(option) = option {
            let (name, value) = rustc_option_parts(option);
            if name == "trust_verify" {
                effective = match value {
                    // A bare `-Ztrust-verify` is rejected by the compiler; a
                    // probe must not read it as either answer.
                    None => None,
                    Some("on") => Some(true),
                    Some("off") => Some(false),
                    Some(_) => None,
                };
            }
        }
        index += consumed;
    }
    effective
}

/// The complete verifier policy that Targo is allowed to carry across
/// Cargo's explicit-target host boundary. Compilation-unit identity is not in
/// this list: Cargo derives and appends role/package metadata later.
///
/// Since T14a this is also the whole Trust vocabulary of the verified lane:
/// `TrustLane::new` refuses a `TRUST_TARGO_LANE_RUSTFLAGS` carrying any
/// `-Ztrust-*` option outside it before a probe or Unit exists, so this one
/// list is the protocol (targo-trust keeps no copy to keep in sync).
/// Every option targo trust hands over comes from the command line, the workspace
/// root's `[trust]` table (the budget options derive from `effort`/`backstop`
/// alone) or the adopted project requirements: TRUSTFLAGS, its per-run
/// override channel until T7a, is not read.
const VERIFIED_TARGO_HOST_POLICY_OPTIONS: &[&str] = &[
    "trust_cg_output_gate",
    // Trust: strict frontend lowering is policy, never verification activation.
    "trust_ir_lower",
    // Trust (platform protocols, plan L1a): the platform pass's policy. The dump-facts sink
    // is deliberately absent: it is a per-compilation test/measurement file, not graph-wide
    // policy, and on this channel every unit would write the same path.
    "trust_platform_budget",
    "trust_platform_properties",
    "trust_platform_report",
    "trust_platform_unanalysed",
    // Trust (D21): the lane's `--no-proc-macro-isolation`. Targo itself passes
    // the option to each unit whose proc-macro TCB is in scope
    // (`trust_proc_macro_expansion`); the lane can only switch that off.
    "trust_proc_macro_isolation",
    "trust_proof_artifact_root",
    // Trust (determinism plan §3.2a/§3.6): the budget profile's one effort
    // count and the two clocks its backstop derives. The step budget is a
    // seal constant no caller sets.
    "trust_verify_effort",
    "trust_policy",
    "trust_verify_function_budget_ms",
    "trust_verify_include_dependencies",
    "trust_verify_level",
    "trust_verify_output",
    "trust_verify_profile",
    "trust_verify_session",
    "trust_verify_timeout_ms",
    "trust_verify_worker_threads",
];

fn is_verified_targo_host_policy_option(name: &str) -> bool {
    VERIFIED_TARGO_HOST_POLICY_OPTIONS.contains(&name)
}

fn is_targo_reserved_unit_option(name: &str) -> bool {
    matches!(
        name,
        "trust_verify_crate_role" | "trust_verify_package_name"
    )
}

fn is_verified_targo_host_safety_option(name: &str) -> bool {
    matches!(name, "overflow_checks" | "debug_assertions")
}

fn rustc_bool_value(value: &str) -> Option<bool> {
    match value {
        "y" | "yes" | "on" | "true" => Some(true),
        "n" | "no" | "off" | "false" => Some(false),
        _ => None,
    }
}

fn extract_verified_targo_host_policy(rustflags: &[String]) -> CargoResult<Vec<String>> {
    let mut policy = Vec::new();
    let mut seen = HashSet::default();
    let mut session = None;
    let mut proof_artifact_root = None;
    let mut index = 0;
    while index < rustflags.len() {
        let (option_class, option, split) = if rustflags[index] == "-Z" {
            let option = rustflags.get(index + 1).ok_or_else(|| {
                anyhow::anyhow!("verified Targo RUSTFLAGS end with an incomplete `-Z` option")
            })?;
            ('Z', Some(option.as_str()), true)
        } else if rustflags[index] == "-C" {
            let option = rustflags.get(index + 1).ok_or_else(|| {
                anyhow::anyhow!("verified Targo RUSTFLAGS end with an incomplete `-C` option")
            })?;
            ('C', Some(option.as_str()), true)
        } else if let Some(option) = rustflags[index]
            .strip_prefix("-Z")
            .filter(|option| !option.is_empty())
        {
            ('Z', Some(option), false)
        } else if let Some(option) = rustflags[index]
            .strip_prefix("-C")
            .filter(|option| !option.is_empty())
        {
            ('C', Some(option), false)
        } else {
            ('\0', None, false)
        };

        let Some(option) = option else {
            index += 1;
            continue;
        };
        let (name, value) = rustc_option_parts(option);
        if option_class == 'Z' {
            if name == "contract_checks" {
                anyhow::bail!(
                    "verified Targo policy cannot contain retired -Zcontract_checks; certified monitors are selected automatically"
                );
            }
            if is_targo_reserved_unit_option(&name) {
                anyhow::bail!(
                    "-Z{name} is reserved for Targo's resolved compilation-unit metadata"
                );
            }
            if name == "trust_verify" {
                anyhow::bail!(
                    "verified Targo policy cannot contain -Ztrust-verify; verification activation is Targo's, not the host's"
                );
            }
            if name.starts_with("trust_") && !is_verified_targo_host_policy_option(&name) {
                anyhow::bail!("-Z{name} is not part of the verified Targo host-policy protocol");
            }
            if is_verified_targo_host_policy_option(&name) {
                if !seen.insert(format!("Z:{name}")) {
                    anyhow::bail!("duplicate verified Targo policy option -Z{name}");
                }
                if name == "trust_verify_session" {
                    let value = value.ok_or_else(|| {
                        anyhow::anyhow!(
                            "-Ztrust-verify-session requires a non-empty, trimmed value"
                        )
                    })?;
                    if value.is_empty() || value.trim() != value {
                        anyhow::bail!("-Ztrust-verify-session requires a non-empty, trimmed value");
                    }
                    session = Some(value.to_string());
                }
                if name == "trust_proof_artifact_root" {
                    let value = value.ok_or_else(|| {
                        anyhow::anyhow!("-Ztrust-proof-artifact-root requires one absolute path")
                    })?;
                    if value.is_empty()
                        || value.trim() != value
                        || !std::path::Path::new(value).is_absolute()
                    {
                        anyhow::bail!(
                            "-Ztrust-proof-artifact-root requires one non-empty, trimmed absolute path"
                        );
                    }
                    proof_artifact_root = Some(value.to_string());
                }
                if split {
                    policy.push("-Z".to_string());
                    policy.push(option.to_string());
                } else {
                    policy.push(rustflags[index].clone());
                }
            }
        } else if is_verified_targo_host_safety_option(&name) {
            let value = value.ok_or_else(|| {
                anyhow::anyhow!("verified Targo safety option -C{name} requires a boolean value")
            })?;
            if rustc_bool_value(value) != Some(true) {
                anyhow::bail!(
                    "verified Targo safety option -C{name} must be enabled, got `{value}`"
                );
            }
            if !seen.insert(format!("C:{name}")) {
                anyhow::bail!("duplicate verified Targo safety option -C{name}");
            }
            if split {
                policy.push("-C".to_string());
                policy.push(option.to_string());
            } else {
                policy.push(rustflags[index].clone());
            }
        }
        index += if split { 2 } else { 1 };
    }

    if session.is_none() {
        anyhow::bail!("verified Targo host policy is missing -Ztrust-verify-session=<nonce>");
    }
    if proof_artifact_root.is_none() {
        anyhow::bail!(
            "verified Targo host policy is missing -Ztrust-proof-artifact-root=<absolute-path>"
        );
    }
    Ok(policy)
}

fn verified_targo_target_codegen_backend(rustflags: &[String]) -> CargoResult<Option<String>> {
    let mut backend = None;
    let mut index = 0;
    while index < rustflags.len() {
        let (option, split) = if rustflags[index] == "-Z" {
            (
                Some(
                    rustflags
                        .get(index + 1)
                        .ok_or_else(|| {
                            anyhow::anyhow!(
                                "verified Targo RUSTFLAGS end with an incomplete `-Z` option"
                            )
                        })?
                        .as_str(),
                ),
                true,
            )
        } else {
            (
                rustflags[index]
                    .strip_prefix("-Z")
                    .filter(|option| !option.is_empty()),
                false,
            )
        };
        if let Some(option) = option {
            let (name, value) = rustc_option_parts(option);
            if name == "codegen_backend" {
                let value = value.filter(|value| !value.is_empty()).ok_or_else(|| {
                    anyhow::anyhow!("verified Targo -Zcodegen-backend requires a non-empty value")
                })?;
                if backend.is_some() {
                    anyhow::bail!("duplicate verified Targo -Zcodegen-backend options");
                }
                backend = Some(canonical_codegen_backend_value(value).to_string());
            }
        }
        index += if split { 2 } else { 1 };
    }
    Ok(backend)
}

// Trust: this is an assertion surface, deliberately smaller than the imported
// protocol. Session, artifact, reporting and unit-scope authority stay private.
fn is_host_trust_policy_assertion(name: &str) -> bool {
    matches!(
        name,
        "trust_policy"
            | "trust_verify_level"
            | "trust_verify_profile"
            | "trust_verify_include_dependencies"
            | "trust_ir_lower"
    )
}

fn reconcile_host_config_trust_policy(
    host_flags: &[String],
    imported_policy: &[String],
) -> CargoResult<Vec<String>> {
    reconcile_lane_trust_policy(host_flags, imported_policy, "[host]")
}

// Trust (T14a): the same assertion rules for the project's configured
// `[target]`/`[build]` rustflags, which now reach a verified compile ahead of
// the lane: a `-Ztrust-*` token there is a requirement assertion that matches
// the lane or refuses the run, and an off-switch is refused. `scope` names the
// tables in every refusal.
fn reconcile_lane_trust_policy(
    host_flags: &[String],
    imported_policy: &[String],
    scope: &str,
) -> CargoResult<Vec<String>> {
    super::super::required_trust_verification_assertion(host_flags).map_err(anyhow::Error::msg)?;
    let mut imported_assertions = HashMap::default();
    for (name, value) in super::super::prefixed_compiler_options(imported_policy, "-Z")
        .map_err(anyhow::Error::msg)?
    {
        if is_host_trust_policy_assertion(&name)
            && imported_assertions.insert(name.clone(), value).is_some()
        {
            anyhow::bail!("duplicate imported host policy -Z{name}");
        }
    }
    let imported_safety_options = imported_policy
        .iter()
        .filter_map(|flag| flag.strip_prefix("-C"))
        .filter(|option| !option.is_empty())
        .map(|option| rustc_option_parts(option).0.into_owned())
        .filter(|name| is_verified_targo_host_safety_option(name))
        .collect::<HashSet<_>>();
    // Split `-C`, `option=value` pairs need a small second pass.
    let mut imported_safety_options = imported_safety_options;
    for pair in imported_policy.windows(2) {
        if pair[0] == "-C" {
            let name = rustc_option_parts(&pair[1]).0.into_owned();
            if is_verified_targo_host_safety_option(&name) {
                imported_safety_options.insert(name);
            }
        }
    }
    let mut seen = HashSet::default();
    let mut sanitized = Vec::with_capacity(host_flags.len());
    let mut index = 0;
    while index < host_flags.len() {
        let (option_class, option, split) = if host_flags[index] == "-Z" {
            ('Z', host_flags.get(index + 1).map(String::as_str), true)
        } else if host_flags[index] == "-C" {
            ('C', host_flags.get(index + 1).map(String::as_str), true)
        } else if let Some(option) = host_flags[index]
            .strip_prefix("-Z")
            .filter(|option| !option.is_empty())
        {
            ('Z', Some(option), false)
        } else if let Some(option) = host_flags[index]
            .strip_prefix("-C")
            .filter(|option| !option.is_empty())
        {
            ('C', Some(option), false)
        } else {
            ('\0', None, false)
        };
        if let Some(option) = option {
            let (name, value) = rustc_option_parts(option);
            if option_class == 'Z' && is_host_trust_policy_assertion(&name) {
                if !seen.insert(name.to_string()) {
                    anyhow::bail!("duplicate {scope} policy assertion -Z{name}");
                }
                let value = value.filter(|value| !value.is_empty()).ok_or_else(|| {
                    anyhow::anyhow!("{scope} policy assertion -Z{name} requires an explicit value")
                })?;
                let expected = imported_assertions
                    .get(name.as_ref())
                    .and_then(Option::as_deref)
                    .filter(|value| !value.is_empty())
                    .ok_or_else(|| {
                        anyhow::anyhow!(
                            "{scope} policy assertion -Z{name} has no explicit imported policy to match"
                        )
                    })?;
                if !project_policy_assertion_matches(name.as_ref(), value, expected) {
                    anyhow::bail!(
                        "{scope} policy assertion -Z{name}={value} does not match imported value `{expected}`"
                    );
                }
                index += if split { 2 } else { 1 };
                continue;
            }
            // A unique explicit positive assertion was validated above. It is
            // retained, not forwarded as activation: the Unit graph checks it
            // before cache reuse, and real compiler argv drops only this token.
            if option_class == 'Z' && name == "trust_verify" {
                sanitized.extend_from_slice(&host_flags[index..index + if split { 2 } else { 1 }]);
                index += if split { 2 } else { 1 };
                continue;
            }
            if option_class == 'Z' && name.starts_with("trust_") {
                anyhow::bail!(
                    "{scope} rustflags cannot set -Z{name} during a verified Targo invocation"
                );
            }
            if option_class == 'C' && imported_safety_options.contains(name.as_ref()) {
                anyhow::bail!(
                    "{scope} rustflags cannot set -C{name} while verified Targo imports that safety policy"
                );
            }
        }
        let consumed = if split && option.is_some() { 2 } else { 1 };
        sanitized.extend_from_slice(&host_flags[index..index + consumed]);
        index += consumed;
    }
    Ok(sanitized)
}

// Trust: the typed project resolver normalizes bool/level spellings. Match
// equivalent assertions without changing duplicate or authority refusal rules.
fn project_policy_assertion_matches(name: &str, actual: &str, expected: &str) -> bool {
    let boolean = |value: &str| match value {
        "on" | "yes" | "true" | "y" => Some(true),
        "off" | "no" | "false" | "n" => Some(false),
        _ => None,
    };
    match name {
        "trust_verify_include_dependencies" => {
            boolean(actual).is_some() && boolean(actual) == boolean(expected)
        }
        "trust_ir_lower" if actual != "strict" && expected != "strict" => {
            boolean(actual).is_some() && boolean(actual) == boolean(expected)
        }
        "trust_verify_level" => {
            actual.parse::<u8>().ok().is_some()
                && actual.parse::<u8>().ok() == expected.parse::<u8>().ok()
        }
        _ => actual == expected,
    }
}

// Trust: ordinary codegen flags retain Cargo's environment precedence: an
// environment value replaces the configured tables in every lane. Only the
// configured Trust requirements survive it: they constrain the lane, never
// supply its session, unit role, or verification activation. `imported_flags`
// is the lane (`TRUST_TARGO_LANE_RUSTFLAGS`) for Rust flags, and the
// environment's own flags for a verified rustdoc invocation.
fn reconcile_overridden_config_trust_policy(
    configured: &[String],
    imported_flags: &[String],
) -> CargoResult<Vec<String>> {
    reject_retired_contract_checks(configured)?;
    let assertions = super::super::prefixed_compiler_options(configured, "-Z")
        .map_err(anyhow::Error::msg)?
        .into_iter()
        .filter(|(name, _)| name.starts_with("trust_") || name.starts_with("no_trust_"))
        .map(|(name, value)| match value {
            Some(value) => format!("-Z{name}={value}"),
            None => format!("-Z{name}"),
        })
        .collect::<Vec<_>>();
    if assertions.is_empty() {
        return Ok(Vec::new());
    }
    let policy = extract_verified_targo_host_policy(imported_flags)?;
    reconcile_host_config_trust_policy(&assertions, &policy).with_context(|| {
        "verified Targo environment flags must satisfy overridden target/build configuration; \
         select the matching authenticated lane (a `targo trust` flag) and project requirement"
    })
}

/// One run of rustflags and where Cargo read it, so a notice about one of its
/// options can name the file, variable or `--config` it came from (T14a).
#[derive(Debug, Clone, PartialEq, Eq)]
struct FlagSource {
    origin: String,
    flags: Vec<String>,
}

/// Gets compiler flags from environment variables.
/// See [`extra_args`] for more.
// Trust: upstream's `rustflags_from_env`, returning the variable that won as
// well, for the lane's notices. Its logic is unchanged.
fn rustflags_from_env_source(gctx: &GlobalContext, flags: Flags) -> Option<FlagSource> {
    // First try CARGO_ENCODED_RUSTFLAGS from the environment.
    // Prefer this over RUSTFLAGS since it's less prone to encoding errors.
    let encoded = format!("CARGO_ENCODED_{}", flags.as_env());
    if let Ok(a) = gctx.get_env(&encoded) {
        let flags = if a.is_empty() {
            Vec::new()
        } else {
            a.split('\x1f').map(str::to_string).collect()
        };
        return Some(FlagSource {
            origin: format!("environment variable `{encoded}`"),
            flags,
        });
    }

    // Then try RUSTFLAGS from the environment
    if let Ok(a) = gctx.get_env(flags.as_env()) {
        let args = a
            .split(' ')
            .map(str::trim)
            .filter(|s| !s.is_empty())
            .map(str::to_string);
        return Some(FlagSource {
            origin: format!("environment variable `{}`", flags.as_env()),
            flags: args.collect(),
        });
    }

    // No rustflags to be collected from the environment
    None
}

/// Gets compiler flags from `[target]` section in the config.
/// See [`extra_args`] for more.
pub(super) fn rustflags_from_target(
    gctx: &GlobalContext,
    host_triple: &str,
    target_cfg: Option<&[Cfg]>,
    kind: CompileKind,
    flag: Flags,
) -> CargoResult<Option<Vec<String>>> {
    let rustflags = rustflags_from_target_sources(gctx, host_triple, target_cfg, kind, flag)?
        .into_iter()
        .flat_map(|source| source.flags)
        .collect::<Vec<_>>();

    if rustflags.is_empty() {
        Ok(None)
    } else {
        Ok(Some(rustflags))
    }
}

// Trust: `rustflags_from_target` table by table, each with its definition, so
// the lane's notices name the file a dropped option came from (T14a). The
// selection and order are upstream's: `target.<triple>`, then every matching
// `target.'cfg(..)'` table.
fn rustflags_from_target_sources(
    gctx: &GlobalContext,
    host_triple: &str,
    target_cfg: Option<&[Cfg]>,
    kind: CompileKind,
    flag: Flags,
) -> CargoResult<Vec<FlagSource>> {
    let mut sources = Vec::new();

    // Then the target.*.rustflags value...
    let target = match &kind {
        CompileKind::Host => host_triple,
        CompileKind::Target(target) => target.short_name(),
    };
    let key = format!("target.{}.{}", target, flag.as_key());
    if let Some(args) = gctx.get::<OptValue<StringList>>(["target", target, flag.as_key()])? {
        sources.push(FlagSource {
            origin: format!("{} (`{key}`)", args.definition),
            flags: args.val.as_slice().to_vec(),
        });
    }
    // ...including target.'cfg(...)'.rustflags
    if let Some(target_cfg) = target_cfg {
        gctx.target_cfgs()?
            .iter()
            .filter_map(|(key, cfg)| match flag {
                Flags::Rust => cfg.rustflags.as_ref().map(|rustflags| (key, rustflags)),
                Flags::Rustdoc => cfg
                    .rustdocflags
                    .as_ref()
                    .map(|rustdocflags| (key, rustdocflags)),
            })
            .filter(|(key, _rustflags)| CfgExpr::matches_key(key, target_cfg))
            .for_each(|(key, cfg_rustflags)| {
                sources.push(FlagSource {
                    origin: format!(
                        "{} (`target.'{key}'.{}`)",
                        cfg_rustflags.definition,
                        flag.as_key()
                    ),
                    flags: cfg_rustflags.val.as_slice().to_vec(),
                });
            });
    }

    Ok(sources)
}

/// Gets compiler flags from `[host]` section in the config.
/// See [`extra_args`] for more.
pub(super) fn rustflags_from_host(
    gctx: &GlobalContext,
    flag: Flags,
    host_triple: &str,
) -> CargoResult<Option<Vec<String>>> {
    Ok(rustflags_from_host_source(gctx, flag, host_triple)?.map(|source| source.flags))
}

// Trust: `rustflags_from_host` with its definition, for the lane's notices.
fn rustflags_from_host_source(
    gctx: &GlobalContext,
    flag: Flags,
    host_triple: &str,
) -> CargoResult<Option<FlagSource>> {
    let target_cfg = gctx.host_cfg_tuple(host_triple)?;
    let list = match flag {
        Flags::Rust => &target_cfg.rustflags,
        Flags::Rustdoc => {
            // host.rustdocflags is not a thing, since it does not make sense
            return Ok(None);
        }
    };
    Ok(list.as_ref().map(|l| FlagSource {
        origin: format!("{} (`[host]` rustflags)", l.definition),
        flags: l.val.as_slice().to_vec(),
    }))
}

/// Gets compiler flags from `[build]` section in the config.
/// See [`extra_args`] for more.
pub(super) fn rustflags_from_build(
    gctx: &GlobalContext,
    flag: Flags,
) -> CargoResult<Option<Vec<String>>> {
    // Then the `build.rustflags` value.
    let build = gctx.build_config()?;
    let list = match flag {
        Flags::Rust => &build.rustflags,
        Flags::Rustdoc => &build.rustdocflags,
    };
    Ok(list.as_ref().map(|l| l.as_slice().to_vec()))
}

// Trust: `rustflags_from_build` with its definition, for the lane's notices.
fn rustflags_from_build_source(
    gctx: &GlobalContext,
    flag: Flags,
) -> CargoResult<Option<FlagSource>> {
    let Some(flags) = rustflags_from_build(gctx, flag)? else {
        return Ok(None);
    };
    let key = format!("build.{}", flag.as_key());
    let origin = match gctx.get::<OptValue<StringList>>(["build", flag.as_key()])? {
        Some(value) => format!("{} (`{key}`)", value.definition),
        None => format!("`{key}`"),
    };
    Ok(Some(FlagSource { origin, flags }))
}

/// Whether a host artifact must take its configuration solely from `[host]` and ignore `[target]`.
pub(crate) fn host_artifact_uses_only_host_config(
    gctx: &GlobalContext,
    requested_kinds: &[CompileKind],
    kind: CompileKind,
) -> CargoResult<bool> {
    let target_applies_to_host = gctx.target_applies_to_host()?;

    // Host artifacts should not generally pick up rustflags from anywhere except [host].
    //
    // The one exception to this is if `target-applies-to-host = true`, which opts into a
    // particular (inconsistent) past Cargo behavior where host artifacts _do_ pick up rustflags
    // set elsewhere when `--target` isn't passed.
    if kind.is_host() {
        if target_applies_to_host && requested_kinds == [CompileKind::Host] {
            // This is the past Cargo behavior where we fall back to the same logic as for other
            // artifacts without --target.
        } else {
            // In all other cases, host artifacts just get flags from [host], regardless of
            // --target. Or, phrased differently, no `--target` behaves the same as `--target
            // <host>`, and host artifacts are always "special" (they don't pick up `RUSTFLAGS` for
            // example).
            return Ok(true);
        }
    }

    Ok(false)
}

/// Collection of information about `rustc` and the host and target.
pub struct RustcTargetData<'gctx> {
    /// Information about `rustc` itself.
    pub rustc: Rustc,

    /// Config
    pub gctx: &'gctx GlobalContext,
    requested_kinds: Vec<CompileKind>,

    /// Build information for the "host", which is information about when
    /// `rustc` is invoked without a `--target` flag. This is used for
    /// selecting a linker, and applying link overrides.
    ///
    /// The configuration read into this depends on whether or not
    /// `target-applies-to-host=true`.
    host_config: TargetConfig,
    /// Information about the host platform.
    host_info: TargetInfo,

    /// Build information for targets that we're building for.
    target_config: HashMap<CompileTarget, TargetConfig>,
    /// Information about the target platform that we're building for.
    target_info: HashMap<CompileTarget, TargetInfo>,
}

/// One configuration owner for real target metadata and preflight selection.
pub(crate) fn target_configuration(
    gctx: &GlobalContext,
    kind: CompileKind,
    host: &str,
) -> CargoResult<TargetConfig> {
    match kind {
        CompileKind::Host if !gctx.target_applies_to_host()? => gctx.host_cfg_tuple(host),
        CompileKind::Host => gctx.target_cfg_tuple(host),
        CompileKind::Target(target) => gctx.target_cfg_tuple(target.short_name()),
    }
}

impl<'gctx> RustcTargetData<'gctx> {
    #[tracing::instrument(skip_all)]
    pub fn new(
        ws: &Workspace<'gctx>,
        requested_kinds: &[CompileKind],
    ) -> CargoResult<RustcTargetData<'gctx>> {
        let gctx = ws.gctx();
        let rustc = gctx.load_global_rustc(Some(ws))?;
        let mut target_config = HashMap::default();
        let mut target_info = HashMap::default();
        let target_applies_to_host = gctx.target_applies_to_host()?;
        let host_target = CompileTarget::new(&rustc.host, gctx.cli_unstable().json_target_spec)?;
        let host_info = TargetInfo::new(gctx, requested_kinds, &rustc, CompileKind::Host)?;

        // This config is used for link overrides and choosing a linker.
        let host_config = target_configuration(gctx, CompileKind::Host, &rustc.host)?;

        // This is a hack. The unit_dependency graph builder "pretends" that
        // `CompileKind::Host` is `CompileKind::Target(host)` if the
        // `--target` flag is not specified. Since the unit_dependency code
        // needs access to the target config data, create a copy so that it
        // can be found. See `rebuild_unit_graph_shared` for why this is done.
        if requested_kinds.iter().any(CompileKind::is_host) {
            target_config.insert(
                host_target,
                target_configuration(gctx, CompileKind::Target(host_target), &rustc.host)?,
            );

            // If target_applies_to_host is true, the host_info is the target info,
            // otherwise we need to build target info for the target.
            if target_applies_to_host {
                target_info.insert(host_target, host_info.clone());
            } else {
                let host_target_info = TargetInfo::new(
                    gctx,
                    requested_kinds,
                    &rustc,
                    CompileKind::Target(host_target),
                )?;
                target_info.insert(host_target, host_target_info);
            }
        };

        let mut res = RustcTargetData {
            rustc,
            gctx,
            requested_kinds: requested_kinds.into(),
            host_config,
            host_info,
            target_config,
            target_info,
        };

        // Get all kinds we currently know about.
        //
        // For now, targets can only ever come from the root workspace
        // units and artifact dependencies, so this
        // correctly represents all the kinds that can happen. When we have
        // other ways for targets to appear at places that are not the root units,
        // we may have to revisit this.
        fn artifact_targets(package: &Package) -> impl Iterator<Item = CompileKind> + '_ {
            package
                .manifest()
                .dependencies()
                .iter()
                .filter_map(|d| d.artifact()?.target()?.to_compile_kind())
        }
        let all_kinds = requested_kinds
            .iter()
            .copied()
            .chain(ws.members().flat_map(|p| {
                p.manifest()
                    .default_kind()
                    .into_iter()
                    .chain(p.manifest().forced_kind())
                    .chain(artifact_targets(p))
            }));
        for kind in all_kinds {
            res.merge_compile_kind(kind)?;
        }

        Ok(res)
    }

    /// Insert `kind` into our `target_info` and `target_config` members if it isn't present yet.
    pub fn merge_compile_kind(&mut self, kind: CompileKind) -> CargoResult<()> {
        if let CompileKind::Target(target) = kind {
            if !self.target_config.contains_key(&target) {
                self.target_config.insert(
                    target,
                    target_configuration(self.gctx, kind, &self.rustc.host)?,
                );
            }
            if !self.target_info.contains_key(&target) {
                self.target_info.insert(
                    target,
                    TargetInfo::new(self.gctx, &self.requested_kinds, &self.rustc, kind)?,
                );
            }
        }
        Ok(())
    }

    /// Returns a "short" name for the given kind, suitable for keying off
    /// configuration in Cargo or presenting to users.
    pub fn short_name<'a>(&'a self, kind: &'a CompileKind) -> &'a str {
        match kind {
            CompileKind::Host => &self.rustc.host,
            CompileKind::Target(target) => target.short_name(),
        }
    }

    /// Whether a dependency should be compiled for the host or target platform,
    /// specified by `CompileKind`.
    pub fn dep_platform_activated(&self, dep: &Dependency, kind: CompileKind) -> bool {
        // If this dependency is only available for certain platforms,
        // make sure we're only enabling it for that platform.
        let Some(platform) = dep.platform() else {
            return true;
        };
        let name = self.short_name(&kind);
        platform.matches(name, self.cfg(kind))
    }

    /// Gets the list of `cfg`s printed out from the compiler for the specified kind.
    pub fn cfg(&self, kind: CompileKind) -> &[Cfg] {
        self.info(kind).cfg()
    }

    /// Information about the given target platform, learned by querying rustc.
    ///
    /// # Panics
    ///
    /// Panics, if the target platform described by `kind` can't be found.
    /// See [`get_info`](Self::get_info) for a non-panicking alternative.
    pub fn info(&self, kind: CompileKind) -> &TargetInfo {
        self.get_info(kind).unwrap()
    }

    /// Information about the given target platform, learned by querying rustc.
    ///
    /// Returns `None` if the target platform described by `kind` can't be found.
    pub fn get_info(&self, kind: CompileKind) -> Option<&TargetInfo> {
        match kind {
            CompileKind::Host => Some(&self.host_info),
            CompileKind::Target(s) => self.target_info.get(&s),
        }
    }

    /// Gets the target configuration for a particular host or target.
    pub fn target_config(&self, kind: CompileKind) -> &TargetConfig {
        match kind {
            CompileKind::Host => &self.host_config,
            CompileKind::Target(s) => &self.target_config[&s],
        }
    }

    pub fn get_unsupported_std_targets(&self) -> Vec<&str> {
        let mut unsupported = Vec::new();
        for (target, target_info) in &self.target_info {
            if target_info.supports_std == Some(false) {
                unsupported.push(target.short_name());
            }
        }
        unsupported
    }

    pub fn requested_kinds(&self) -> &[CompileKind] {
        &self.requested_kinds
    }
}

// Trust: pins the resolved-flags policy layer above. These are unit tests over
// pure functions precisely so the boundary can be exercised without a workspace
// or a compiler, which the `tests/testsuite` integration tests both need.
#[cfg(test)]
mod trust_fast_lint_tests {
    use std::ffi::OsStr;

    use super::{
        FlagSource, Flags, TargetInfoProbeLane, TrustLane, add_trust_verify_cfg,
        append_trust_no_verify_fast_flag, decode_lane_rustflags,
        extract_verified_targo_host_policy, reconcile_host_config_trust_policy,
        reconcile_overridden_config_trust_policy, reject_retired_contract_checks,
        reports_trust_verify, target_info_probe_flags, trust_verify_default_query_flags,
        unverified_lane_rustdoc_flags, verified_targo_named_target_error,
        verified_targo_target_codegen_backend,
    };
    use crate::compiler::{CompileKind, CompileTarget};

    fn strings(values: &[&str]) -> Vec<String> {
        values.iter().map(|value| (*value).to_string()).collect()
    }

    #[test]
    fn verified_target_origin_uses_exact_builtin_membership() {
        let builtins = "aarch64-unknown-linux-gnu\nx86_64-unknown-linux-gnu\n";
        assert_eq!(
            verified_targo_named_target_error(
                CompileKind::Target(CompileTarget::Tuple("x86_64-unknown-linux-gnu".into())),
                "x86_64-unknown-linux-gnu",
                builtins,
            ),
            None
        );
        for target in [
            "x86_64-unknown-linux-gnu.json",
            "X86_64-unknown-linux-gnu",
            "x86_64-unknown-linux-gnu ",
            "workspace-shadow-target",
        ] {
            let error = verified_targo_named_target_error(
                CompileKind::Target(CompileTarget::Tuple(target.into())),
                "x86_64-unknown-linux-gnu",
                builtins,
            )
            .expect("non-exact or non-built-in tuple must not enter named target search");
            assert!(error.contains("named non-built-in target"), "{error}");
            assert!(error.contains("RUST_TARGET_PATH"), "{error}");
        }
        assert_eq!(
            verified_targo_named_target_error(
                CompileKind::Target(CompileTarget::Json {
                    short: "custom".into(),
                    path: "/tmp/custom.json".into(),
                }),
                "x86_64-unknown-linux-gnu",
                builtins,
            ),
            None,
            "explicit JSON follows the separate exact-byte binding"
        );
        assert_eq!(
            verified_targo_named_target_error(
                CompileKind::Host,
                "x86_64-unknown-linux-gnu",
                builtins,
            ),
            None
        );
        let invalid_host =
            verified_targo_named_target_error(CompileKind::Host, "workspace-shadow-host", builtins)
                .expect("compiler host must also name an exact built-in target");
        assert!(
            invalid_host.contains("workspace-shadow-host"),
            "{invalid_host}"
        );
    }

    #[test]
    fn native_fast_lane_disables_verification_for_rustc_and_rustdoc_once() {
        let mut args = vec!["-Cdebuginfo=1".to_string()];
        append_trust_no_verify_fast_flag(&mut args, true);
        append_trust_no_verify_fast_flag(&mut args, true);
        assert_eq!(
            args,
            ["-Cdebuginfo=1", "-Ztrust-verify=off"].map(String::from)
        );

        let mut split = strings(&["-Z", "trust-verify=off"]);
        append_trust_no_verify_fast_flag(&mut split, true);
        assert_eq!(split, strings(&["-Z", "trust-verify=off"]));

        let mut explicitly_enabled = strings(&["-Ztrust-verify=on"]);
        append_trust_no_verify_fast_flag(&mut explicitly_enabled, true);
        assert_eq!(
            explicitly_enabled,
            strings(&["-Ztrust-verify=on", "-Ztrust-verify=off"])
        );

        let mut rustc_equivalent = strings(&["-Ztrust_verify=off"]);
        append_trust_no_verify_fast_flag(&mut rustc_equivalent, true);
        assert_eq!(rustc_equivalent, strings(&["-Ztrust_verify=off"]));

        let mut later_enable = strings(&["-Ztrust-verify=off", "-Z", "trust_verify=on"]);
        append_trust_no_verify_fast_flag(&mut later_enable, true);
        assert_eq!(
            later_enable,
            strings(&[
                "-Ztrust-verify=off",
                "-Z",
                "trust_verify=on",
                "-Ztrust-verify=off"
            ])
        );

        let mut later_disable = strings(&["-Ztrust-verify=on", "-Z", "trust_verify=off"]);
        append_trust_no_verify_fast_flag(&mut later_disable, true);
        assert_eq!(
            later_disable,
            strings(&["-Ztrust-verify=on", "-Z", "trust_verify=off"])
        );
    }

    #[test]
    fn target_info_probe_strips_every_rustc_equivalent_trust_option_spelling_only() {
        let flags = strings(&[
            "-Cdebuginfo=2",
            "-Ztrust-verify-session=combined-hyphen",
            "-Ztrust_verify_output=json",
            "-Z",
            "trust-proof-artifact-root=/tmp/proof",
            "-Z",
            "trust_cg_output_gate=strict",
            "-Ztrust-policy=advisory",
            "-Ztrust_ir_lower",
            "-Ztrust_verify=on",
            "-Zcodegen-backend=trust-cg",
            "--cfg",
            "trustworthy_target_probe",
        ]);

        assert_eq!(
            target_info_probe_flags(&flags, TargetInfoProbeLane::CompilerDefault),
            strings(&[
                "-Cdebuginfo=2",
                "-Zcodegen-backend=trust-cg",
                "--cfg",
                "trustworthy_target_probe",
            ])
        );
        assert_eq!(
            flags[0], "-Cdebuginfo=2",
            "the retained policy is immutable"
        );
    }

    /// Trust (DECISION_QUEUE TARGO-PROBE-MIR-1): the probe runs at the
    /// compiler's default, a proof session on a `trustc` that verifies by
    /// default, so it drops every MIR-pipeline option a proof session refuses
    /// (`rustc_session::trust_mir_pipeline_option_refusal`), in each spelling
    /// rustc accepts. MIR options T6 does not refuse, and everything else, stay.
    /// Before, `targo --unverified build` with `RUSTFLAGS=-Zinline-mir` aborted
    /// at the probe on such a compiler.
    #[test]
    fn target_info_probe_drops_the_mir_pipeline_options_a_proof_session_refuses() {
        let flags = strings(&[
            "-Cdebuginfo=2",
            "-Zinline-mir",
            "-Zinline_mir=no",
            "-Z",
            "mir-opt-level=1",
            "-Zmir_opt_level=4",
            "-Zinline-mir-threshold=50",
            "-Z",
            "inline_mir_hint_threshold=100",
            "-Zinline-mir-forwarder-threshold=3",
            "-Zmir-enable-passes=+Inline",
            "-Zmir-opt-bisect-limit=0",
            "-Zmir-preserve-ub",
            "-Zmir_strip_debuginfo=locals-in-tiny-functions",
            "-Zinline-mir-preserve-debug",
            "-Z",
            "validate-mir",
            "-Ztrust-verify=off",
            "-Zthreads=4",
            "--cfg",
            "inline_mir",
        ]);

        assert_eq!(
            target_info_probe_flags(&flags, TargetInfoProbeLane::CompilerDefault),
            strings(&[
                "-Cdebuginfo=2",
                "-Zinline-mir-preserve-debug",
                "-Z",
                "validate-mir",
                "-Zthreads=4",
                "--cfg",
                "inline_mir",
            ])
        );
    }

    /// Trust (TARGO-PROBE-OPERAND-1): only `-Z` options are classified, joined
    /// or split. The operand of another option is never read as one, even when
    /// it starts with `trust_`/`trust-`: it used to be dropped, and the
    /// value-taking option left behind took the probe's next argument
    /// (`RUSTFLAGS="--cfg trust_x"` failed every Targo build at the probe).
    #[test]
    fn target_info_probe_never_reads_an_operand_as_an_option() {
        let flags = strings(&[
            "--cfg",
            "trust_x",
            "--cfg",
            "trust-feature=\"on\"",
            "-l",
            "trust_native",
            "-A",
            "trust-lint",
            "--cfg=trust_y",
            "-Z",
            "threads=2",
        ]);
        assert_eq!(
            target_info_probe_flags(&flags, TargetInfoProbeLane::CompilerDefault),
            flags
        );
    }

    /// Trust (DECISION_QUEUE TARGO-PROBE-LANE-1): the explicitly unverified
    /// lane's probe keeps the lane's off-switch, last, so it answers as the
    /// lane's units compile: `-Zcontract-checks` stays (the units accept it and
    /// carry `cfg(contract_checks)`), and with `-Copt-level=3` the probe no
    /// longer reports the cfgs verification forces on. It still drops every
    /// other Trust option and the MIR-pipeline options. Before, the off-switch
    /// was dropped with the rest.
    #[test]
    fn the_unverified_lane_probe_keeps_the_lane_off_switch_last() {
        let unverified = TargetInfoProbeLane::ExplicitlyUnverified;
        // The lane's resolved flags: the caller's, then Targo's off-switch.
        let lane = strings(&[
            "-Copt-level=3",
            "-Zcontract-checks",
            "-Ztrust-verify-level=2",
            "-Zinline-mir",
            "--cfg",
            "trust_x",
            "-Ztrust-verify=off",
        ]);
        assert!(unverified.keeps_off_switch(&lane));
        assert_eq!(
            target_info_probe_flags(&lane, unverified),
            strings(&[
                "-Copt-level=3",
                "-Zcontract-checks",
                "--cfg",
                "trust_x",
                "-Ztrust-verify=off",
            ])
        );
        // The caller's own off-switch, in any spelling rustc accepts, is the
        // lane's final one when Targo appends none; the probe keeps it as
        // Targo's canonical spelling, after every other flag.
        for own in [
            strings(&["-Z", "trust_verify=off", "-Cdebuginfo=1"]),
            strings(&["-Ztrust_verify=on", "-Ztrust-verify=off", "-Cdebuginfo=1"]),
        ] {
            assert_eq!(
                target_info_probe_flags(&own, unverified),
                strings(&["-Cdebuginfo=1", "-Ztrust-verify=off"]),
                "{own:?}"
            );
        }
        // The probe follows the flags' last-wins answer, as the units do: no
        // off-switch where the final spelling turns verification on (the lane
        // itself never ends so: Targo appends its off-switch after it).
        let verifying = strings(&["-Ztrust-verify=off", "-Ztrust-verify=on"]);
        assert!(!unverified.keeps_off_switch(&verifying));
        assert!(target_info_probe_flags(&verifying, unverified).is_empty());
        // Every other lane (verified Targo, ordinary Cargo) drops it, as before.
        let other = TargetInfoProbeLane::CompilerDefault;
        assert!(!other.keeps_off_switch(&lane));
        assert_eq!(
            target_info_probe_flags(&lane, other),
            strings(&["-Copt-level=3", "-Zcontract-checks", "--cfg", "trust_x"])
        );
    }

    /// Trust (DECISION_QUEUE TARGO-PROBE-LANE-1): the default `trust_verify`
    /// query runs at the compiler's default, so it drops the whole Trust family
    /// (`-Ztrust-*` and the `-Zno-trust-*` alias, the lane's off-switch
    /// included) and every option a Trust compilation refuses: the MIR-pipeline
    /// options (T6) and `-Zcontract-checks` and `-Zlink-only`, in each spelling
    /// rustc accepts. Operands and every other option stay.
    #[test]
    fn the_default_trust_verify_query_drops_the_trust_family_and_the_refused_options() {
        let flags = strings(&[
            "-Copt-level=3",
            "-Zcontract-checks",
            "-Z",
            "contract_checks=yes",
            "-Zlink-only",
            "-Zlink_only=no",
            "-Zno-trust-verify",
            "-Z",
            "no_trust_verify",
            "-Ztrust-verify-level=2",
            "-Z",
            "trust-verify-session=nonce",
            "-Zinline-mir",
            "-Z",
            "mir_opt_level=2",
            "-Zthreads=4",
            "-Zub-checks=no",
            "--cfg",
            "clean_islands",
            "--cfg",
            "contract_checks",
            "--cfg",
            "trust_x",
            "-Ztrust-verify=off",
        ]);
        assert_eq!(
            trust_verify_default_query_flags(&flags),
            strings(&[
                "-Copt-level=3",
                "-Zthreads=4",
                "-Zub-checks=no",
                "--cfg",
                "clean_islands",
                "--cfg",
                "contract_checks",
                "--cfg",
                "trust_x",
            ])
        );
    }

    /// Only the default query's `trust_verify` line is read, and the probe's
    /// cfg set gets it once, where rustc's sorted `--print=cfg` lists it.
    #[test]
    fn the_default_query_adds_only_trust_verify_where_rustc_lists_it() {
        assert!(reports_trust_verify(
            "debug_assertions\noverflow_checks\ntrust_verify\nub_checks\nunix\n"
        ));
        for output in [
            "",
            "debug_assertions\nunix\n",
            "trust_verify_x\n",
            "trust_verify=\"on\"\n",
        ] {
            assert!(!reports_trust_verify(output), "{output:?}");
        }

        let parse = |lines: &[&str]| -> Vec<cargo_platform::Cfg> {
            lines.iter().map(|line| line.parse().unwrap()).collect()
        };
        let mut cfg = parse(&["panic=\"unwind\"", "target_os=\"macos\"", "unix"]);
        add_trust_verify_cfg(&mut cfg).unwrap();
        add_trust_verify_cfg(&mut cfg).unwrap();
        assert_eq!(
            cfg,
            parse(&[
                "panic=\"unwind\"",
                "target_os=\"macos\"",
                "trust_verify",
                "unix"
            ])
        );
    }

    /// ay's committed certify posture (`[target.'cfg(all())'] rustdocflags`),
    /// plus every spelling rustc treats as the same `-Ztrust-*` option and
    /// non-Trust neighbours that must survive untouched.
    fn consumer_rustdocflags() -> Vec<String> {
        strings(&[
            "-Ztrust-verify=on",
            "-Ztrust-policy=certify",
            "-Ztrust-verify-level=2",
            "-Ztrust-verify-profile=unix_hardened",
            "-Ztrust-verify-include-dependencies=yes",
            "-Ztrust-ir-lower=strict",
            "--cfg",
            "trust_docs",
            "-Z",
            "trust_verify=on",
            "-Ztrust_policy=advisory",
            "-Zunstable-options",
            "-Z",
            "unstable-options",
            "-Ztrust-verify=off",
            "-Ztrust-ir-lower",
            "--document-private-items",
        ])
    }

    /// The final argv tail `extra_args` resolves for a rustdoc unit: the lane
    /// filter, then the native off-switch, in that order.
    fn resolved_rustdocflags(
        configured: Vec<String>,
        no_verify_fast: bool,
        verified_targo: bool,
    ) -> Vec<String> {
        let mut args = unverified_lane_rustdoc_flags(configured, no_verify_fast, verified_targo);
        append_trust_no_verify_fast_flag(&mut args, no_verify_fast);
        args
    }

    fn trust_options(args: &[String]) -> Vec<String> {
        let mut found = Vec::new();
        let mut index = 0;
        while index < args.len() {
            let option = if args[index] == "-Z" {
                index += 1;
                args.get(index).map(String::as_str)
            } else {
                args[index].strip_prefix("-Z")
            };
            if let Some(option) = option {
                if option.replace('-', "_").starts_with("trust_") {
                    found.push(option.to_string());
                }
            }
            index += 1;
        }
        found
    }

    #[test]
    fn unverified_lane_rustdoc_and_doctest_argv_carry_no_configured_trust_option() {
        // trustdoc's embedded `EmbeddedNoOfficialEvidence` frontend refused
        // every `-Ztrust-*` but the redundant off-switch, so before this filter
        // `targo --unverified test --doc` on ay ran no doctest at all.
        let resolved = resolved_rustdocflags(consumer_rustdocflags(), true, false);
        assert_eq!(
            resolved,
            strings(&[
                "--cfg",
                "trust_docs",
                "-Zunstable-options",
                "-Z",
                "unstable-options",
                "--document-private-items",
                "-Ztrust-verify=off",
            ]),
            "config/env -Ztrust-* dropped, non-Trust flags kept in order"
        );
        // The only Trust token left is Targo's own off-switch: trustdoc accepts
        // it and forwards it to each doctest compile, which is what keeps the
        // generated doctest crate unverified in a lane that claims nothing.
        assert_eq!(trust_options(&resolved), strings(&["trust-verify=off"]));

        // Without any configured Trust flag the lane still states it once.
        assert_eq!(
            resolved_rustdocflags(strings(&["--cfg", "docsrs"]), true, false),
            strings(&["--cfg", "docsrs", "-Ztrust-verify=off"])
        );
        // A dangling `-Z` is not a Trust option and is left for rustdoc to
        // reject, exactly as before.
        assert_eq!(
            resolved_rustdocflags(strings(&["-Z"]), true, false),
            strings(&["-Z", "-Ztrust-verify=off"])
        );
    }

    #[test]
    fn verified_and_plain_cargo_rustdoc_flags_are_unchanged() {
        // The authenticated `targo trust` lane: byte for byte, so its doctest
        // refusal and census see exactly the configured policy.
        let configured = consumer_rustdocflags();
        assert_eq!(
            unverified_lane_rustdoc_flags(configured.clone(), false, true),
            configured
        );
        // Defence in depth: even if both markers were set, the verified lane
        // wins and nothing is stripped.
        assert_eq!(
            unverified_lane_rustdoc_flags(configured.clone(), true, true),
            configured
        );
        assert_eq!(
            resolved_rustdocflags(configured.clone(), false, true),
            configured
        );
        // Plain Cargo compatibility (no lane marker): Cargo adds and removes
        // no Trust flag of its own.
        assert_eq!(
            resolved_rustdocflags(configured.clone(), false, false),
            configured
        );
    }

    #[test]
    fn verified_lane_does_not_inject_the_native_off_switch() {
        let mut args = Vec::new();
        append_trust_no_verify_fast_flag(&mut args, false);
        assert!(args.is_empty());
    }

    /// One representative compiler token per allowlisted host-policy option.
    /// Options the extractor validates by value get their canonical shapes; a
    /// newly allowlisted option is exercised automatically as `-Z<name>=x`.
    fn representative_host_policy_option(name: &str) -> String {
        let key = name.replace('_', "-");
        match name {
            "trust_policy" => format!("-Z{key}=advisory"),
            // Trust: exercise the real strict selector, not an arbitrary value.
            "trust_ir_lower" => format!("-Z{key}=strict"),
            "trust_cg_output_gate" => format!("-Z{key}=strict"),
            "trust_verify_session" => format!("-Z{key}=proof-full-policy"),
            "trust_proof_artifact_root" => format!("-Z{key}=/tmp/trust-proof-full-policy"),
            "trust_verify_output" => format!("-Z{key}=json"),
            "trust_verify_level" => format!("-Z{key}=2"),
            // Trust (platform protocols): values the compiler accepts.
            "trust_platform_budget" => format!("-Z{key}=1000000"),
            "trust_platform_properties" => format!("-Z{key}=fd-inherit"),
            "trust_platform_report" => format!("-Z{key}=verbose"),
            "trust_platform_unanalysed" => format!("-Z{key}=deny"),
            "trust_proc_macro_isolation" => format!("-Z{key}=no"),
            _ => format!("-Z{key}=x"),
        }
    }

    #[test]
    fn resolved_rustflags_reject_retired_contract_checks_before_target_info_probes() {
        for retired in [
            strings(&["-Zcontract-checks"]),
            strings(&["-Zcontract-checks=yes"]),
            strings(&["-Zcontract_checks=no"]),
            strings(&["-Z", "contract_checks=unexpected"]),
        ] {
            let error = reject_retired_contract_checks(&retired).expect_err(
                "resolved retired projection must fail before a rustc probe is spawned",
            );
            assert!(
                error.to_string().contains("retired -Zcontract_checks"),
                "{error:#}"
            );
            assert!(
                error.to_string().contains("certified monitors"),
                "{error:#}"
            );
        }

        reject_retired_contract_checks(&strings(&[
            "--cfg",
            "contract_checks=metadata-only",
            "-Cmetadata=contract-checks=yes",
        ]))
        .expect("non-option substrings are unrelated metadata");

        let error = extract_verified_targo_host_policy(&strings(&[
            "-Ztrust-verify-session=proof",
            "-Ztrust-proof-artifact-root=/tmp/proof",
            "-Zcontract_checks=false",
        ]))
        .expect_err("the cross-target host-policy import must not silently drop the option");
        assert!(
            error.to_string().contains("retired -Zcontract_checks"),
            "{error:#}"
        );
    }

    #[test]
    fn cross_target_host_policy_preserves_the_complete_closed_protocol() {
        // The fixture is rendered from the production allowlist so it pins the
        // policy → flags rendering itself: extending (or shrinking) the closed
        // protocol updates this test without a hand-maintained magic string
        // list drifting out of sync.
        let mut rustflags = strings(&[
            "-C",
            "target-cpu=native",
            "-Coverflow-checks=yes",
            "-C",
            "debug-assertions=yes",
            "-Zcodegen-backend=trust-cg",
        ]);
        let mut expected = strings(&["-Coverflow-checks=yes", "-C", "debug-assertions=yes"]);
        for name in super::VERIFIED_TARGO_HOST_POLICY_OPTIONS {
            let option = representative_host_policy_option(name);
            // Exercise both getopts spellings: split `-Z <option>` for the
            // first entry, compact `-Z<option>` for the rest.
            if *name == "trust_cg_output_gate" {
                let payload = option
                    .strip_prefix("-Z")
                    .expect("representative options use the -Z prefix")
                    .to_string();
                rustflags.push("-Z".to_string());
                rustflags.push(payload.clone());
                expected.push("-Z".to_string());
                expected.push(payload);
            } else {
                rustflags.push(option.clone());
                expected.push(option);
            }
        }
        let policy = extract_verified_targo_host_policy(&rustflags).unwrap();
        assert_eq!(policy, expected);
    }

    // Trust: policy transport preserves the exact lowering request, but does
    // not relax host-config authority rejection or confer rustdoc coverage.
    #[test]
    fn strict_lowering_policy_crosses_the_lane_transport() {
        let authority = [
            "-Ztrust-verify-session=proof-lowering",
            "-Ztrust-proof-artifact-root=/tmp/proof-lowering",
        ];
        for flags in [
            strings(&["-Ztrust-ir-lower=strict"]),
            strings(&["-Z", "trust-ir-lower=strict"]),
            strings(&["-Ztrust_ir_lower=strict"]),
            strings(&["-Z", "trust_ir_lower=strict"]),
        ] {
            let mut expected = strings(&authority);
            expected.extend(flags);
            let encoded = expected.join("\x1f");
            let lane = decode_lane_rustflags(Some(OsStr::new(&encoded)))
                .expect("the lane is valid Unicode");
            let lane = TrustLane::new(true, false, Flags::Rust, lane)
                .expect("strict lowering must survive the lane transport");
            assert_eq!(lane.host_policy, expected);
            assert_eq!(lane.rustflags.as_deref(), Some(expected.as_slice()));
            // Outside the verified lane the same tokens are refused, never
            // silently imported.
            let unverified = decode_lane_rustflags(Some(OsStr::new(&encoded))).unwrap();
            assert!(TrustLane::new(false, true, Flags::Rust, unverified).is_err());
        }
    }

    // Trust: unlike targo-trust's requirement merge (which replaces an earlier
    // spelling), the authenticated final vector rejects duplicate policy
    // rather than interpreting ambiguous authority.
    #[test]
    fn strict_lowering_policy_refuses_duplicates_activation_and_conflicting_host_config() {
        let policy = strings(&[
            "-Ztrust-verify-session=proof-lowering",
            "-Ztrust-proof-artifact-root=/tmp/proof-lowering",
            "-Ztrust-ir-lower=strict",
        ]);
        extract_verified_targo_host_policy(&policy).expect("baseline strict lowering policy");
        for (extra, diagnostic) in [
            ("-Ztrust_ir_lower=strict", "duplicate"),
            ("-Ztrust_ir_lower=off", "duplicate"),
            ("-Ztrust-verify=on", "activation is Targo's"),
            ("-Ztrust_verify=off", "activation is Targo's"),
            ("-Ztrust-verify-crate-role=primary", "reserved for Targo"),
            ("-Ztrust_verify_package_name=forged", "reserved for Targo"),
        ] {
            let mut forged = policy.clone();
            forged.push(extra.to_string());
            let error = extract_verified_targo_host_policy(&forged)
                .expect_err("strict lowering cannot admit competing policy or unit authority");
            assert!(error.to_string().contains(diagnostic), "{extra}: {error:#}");
        }
        assert!(
            reconcile_host_config_trust_policy(&strings(&["-Ztrust-ir-lower=strict"]), &policy)
                .unwrap()
                .is_empty()
        );
        let error =
            reconcile_host_config_trust_policy(&strings(&["-Ztrust_ir_lower=off"]), &policy)
                .expect_err("host assertions may not change imported policy");
        assert!(
            error.to_string().contains("does not match imported"),
            "{error:#}"
        );
    }

    // Trust (platform protocols, plan L1a; FC-7), adversarial: the host-policy boundary. The
    // four platform policy controls cross it in every getopts spelling with their VALUE
    // untouched (trustc's option parser is what refuses a misspelt or unsupported property, so
    // nothing here may drop or normalize one). A misspelt name, a control the design names that
    // this trustc lacks, the per-compilation facts sink and a duplicate across spellings are
    // refused before a compiler runs, and `[host]` rustflags may set none of them.
    #[test]
    fn platform_policy_crosses_the_host_boundary_exactly() {
        let authority = strings(&[
            "-Ztrust-verify-session=proof-platform",
            "-Ztrust-proof-artifact-root=/tmp/proof-platform",
        ]);
        for flags in [
            strings(&[
                "-Ztrust-platform-properties=fd-inherit",
                "-Ztrust-platform-unanalysed=deny",
                "-Ztrust-platform-budget=5",
                "-Ztrust-platform-report=verbose",
            ]),
            strings(&["-Z", "trust_platform_properties=lock-release"]),
            strings(&["-Ztrust-platform-properties=FD-INHERIT"]),
            strings(&["-Ztrust-platform-properties="]),
        ] {
            let mut policy = authority.clone();
            policy.extend(flags);
            assert_eq!(
                extract_verified_targo_host_policy(&policy)
                    .expect("platform policy is host-boundary protocol"),
                policy,
                "the value must reach trustc verbatim"
            );
        }

        for (extra, diagnostic) in [
            (
                &["-Ztrust-platform-property=fd-inherit"][..],
                "not part of the verified",
            ),
            (
                &["-Ztrust-platform-unanalyzed=deny"][..],
                "not part of the verified",
            ),
            (
                &["-Ztrust-platform=fd-inherit"][..],
                "not part of the verified",
            ),
            (
                &["-Ztrust-platform-premises=fd-bound"][..],
                "not part of the verified",
            ),
            (
                &["-Ztrust-platform-dump-facts=/tmp/facts"][..],
                "not part of the verified",
            ),
            (
                &["-Z", "trust_platform_dump_facts=/tmp/facts"][..],
                "not part of the verified",
            ),
            (
                &[
                    "-Ztrust-platform-properties=fd-inherit",
                    "-Ztrust_platform_properties=fd-inherit",
                ][..],
                "duplicate",
            ),
            (
                &[
                    "-Ztrust-platform-unanalysed=deny",
                    "-Z",
                    "trust-platform-unanalysed=warn",
                ][..],
                "duplicate",
            ),
        ] {
            let mut forged = authority.clone();
            forged.extend(strings(extra));
            let error = extract_verified_targo_host_policy(&forged)
                .expect_err("a misspelt, unscheduled or duplicate platform control is refused");
            assert!(
                error.to_string().contains(diagnostic),
                "{extra:?}: {error:#}"
            );
        }

        let mut policy = authority.clone();
        policy.push("-Ztrust-platform-properties=fd-inherit".to_string());
        extract_verified_targo_host_policy(&policy).expect("baseline platform policy");
        for host in [
            "-Ztrust-platform-properties=fd-inherit",
            "-Ztrust_platform_unanalysed=deny",
            "-Ztrust-platform-dump-facts=/tmp/facts",
        ] {
            let error = reconcile_host_config_trust_policy(&strings(&[host]), &policy)
                .expect_err("[host] rustflags cannot carry platform policy");
            assert!(
                error.to_string().contains("cannot set"),
                "{host}: {error:#}"
            );
        }
    }

    // Trust: assertions have no authority. Five settings must match the actual
    // imported policy; only the verification requirement survives in Unit flags.
    #[test]
    fn host_policy_assertions_match_exact_imported_values_and_retain_requirement() {
        let options = [
            "trust-policy=certify",
            "trust-verify-level=2",
            "trust-verify-profile=unix_hardened",
            "trust-verify-include-dependencies=yes",
            "trust-ir-lower=strict",
        ];
        let policy = options
            .iter()
            .map(|option| format!("-Z{option}"))
            .collect::<Vec<_>>();
        for split in [false, true] {
            for underscores in [false, true] {
                let mut host = strings(&["-Ctarget-cpu=native"]);
                for option in std::iter::once("trust-verify=on").chain(options) {
                    let option = if underscores {
                        option.replace('-', "_")
                    } else {
                        option.to_string()
                    };
                    if split {
                        host.extend(["-Z".to_string(), option]);
                    } else {
                        host.push(format!("-Z{option}"));
                    }
                }
                let sanitized = reconcile_host_config_trust_policy(&host, &policy).unwrap();
                let mut expected = strings(&["-Ctarget-cpu=native"]);
                let assertion = if underscores {
                    "trust_verify=on"
                } else {
                    "trust-verify=on"
                };
                if split {
                    expected.extend(["-Z".to_string(), assertion.to_string()]);
                } else {
                    expected.push(format!("-Z{assertion}"));
                }
                assert_eq!(sanitized, expected);
                assert_eq!(
                    target_info_probe_flags(&sanitized, TargetInfoProbeLane::CompilerDefault),
                    strings(&["-Ctarget-cpu=native"])
                );
            }
        }
    }

    #[test]
    fn host_policy_assertions_refuse_missing_duplicate_mismatched_and_forged_values() {
        let policy = strings(&["-Ztrust-ir-lower=strict", "-Ztrust-verify-level=2"]);
        for (host, expected) in [
            (strings(&["-Ztrust-ir-lower=off"]), "does not match"),
            (strings(&["-Ztrust-ir-lower"]), "explicit value"),
            (strings(&["-Ztrust-ir-lower="]), "explicit value"),
            (strings(&["-Ztrust-policy=certify"]), "no explicit imported"),
            (
                strings(&["-Ztrust-ir-lower=strict", "-Z", "trust_ir_lower=strict"]),
                "duplicate",
            ),
            (
                strings(&["-Ztrust-verify=on", "-Ztrust_verify=true"]),
                "duplicate",
            ),
            (
                strings(&["-Ztrust-verify=off"]),
                "resolved compilation-unit scope",
            ),
            (
                strings(&["-Zno_trust_verify=off"]),
                "resolved compilation-unit scope",
            ),
            (strings(&["-Ztrust-verify"]), "explicit positive"),
            (strings(&["-Ztrust-verify-session=forged"]), "cannot set"),
            (
                strings(&["-Ztrust-proof-artifact-root=/tmp/forged"]),
                "cannot set",
            ),
            (
                strings(&["-Ztrust-verify-crate-role=primary"]),
                "cannot set",
            ),
            (
                strings(&["-Ztrust-verify-package-name=forged"]),
                "cannot set",
            ),
            (strings(&["-Ztrust-verify-output=json"]), "cannot set"),
            (strings(&["-Ztrust-targo-test-monitor"]), "cannot set"),
        ] {
            let error = reconcile_host_config_trust_policy(&host, &policy).unwrap_err();
            assert!(error.to_string().contains(expected), "{host:?}: {error:#}");
        }
    }

    // Trust: native target/build assertions remain requirements even when the
    // frontend-owned environment wins Cargo's ordinary flag precedence.
    #[test]
    fn overridden_config_requirements_match_and_preserve_only_unit_assertion() {
        let policy = strings(&[
            "-Ztrust-verify-session=proof-config",
            "-Ztrust-proof-artifact-root=/tmp/proof-config",
            "-Ztrust-policy=certify",
            "-Ztrust-verify-level=2",
            "-Ztrust-verify-profile=unix_hardened",
            "-Ztrust-verify-include-dependencies=yes",
            "-Ztrust-ir-lower=strict",
        ]);
        let configured = strings(&[
            "-Ctarget-cpu=native",
            "-Coverflow-checks=off",
            "-Z",
            "trust_verify=on",
            "-Ztrust-policy=certify",
            "-Ztrust-verify-level=2",
            "-Ztrust-verify-profile=unix_hardened",
            "-Z",
            "trust_verify_include_dependencies=yes",
            "-Ztrust_ir_lower=strict",
        ]);
        assert_eq!(
            reconcile_overridden_config_trust_policy(&configured, &policy).unwrap(),
            strings(&["-Ztrust_verify=on"]),
        );
        assert_eq!(
            configured.first().map(String::as_str),
            Some("-Ctarget-cpu=native"),
            "configuration is read without being rewritten",
        );
    }

    #[test]
    fn overridden_config_refuses_missing_or_mismatched_policy() {
        let protocol = strings(&[
            "-Ztrust-verify-session=proof-config",
            "-Ztrust-proof-artifact-root=/tmp/proof-config",
        ]);
        for (name, value) in [
            ("trust-policy", "certify"),
            ("trust-verify-level", "2"),
            ("trust-verify-profile", "unix_hardened"),
            ("trust-verify-include-dependencies", "yes"),
            ("trust-ir-lower", "strict"),
        ] {
            let configured = vec![format!("-Z{name}={value}")];
            let missing = reconcile_overridden_config_trust_policy(&configured, &protocol)
                .expect_err("an overridden requirement must not disappear");
            assert!(format!("{missing:#}").contains("no explicit imported"));
            let mut mismatched = protocol.clone();
            mismatched.push(format!("-Z{name}=other"));
            let error = reconcile_overridden_config_trust_policy(&configured, &mismatched)
                .expect_err("configuration cannot silently override authenticated policy");
            assert!(format!("{error:#}").contains("does not match"));
        }
    }

    #[test]
    fn overridden_config_cannot_forge_activation_session_or_duplicate_assertions() {
        let policy = strings(&[
            "-Ztrust-verify-session=proof-config",
            "-Ztrust-proof-artifact-root=/tmp/proof-config",
            "-Ztrust-policy=certify",
        ]);
        for configured in [
            strings(&["-Ztrust-verify=off"]),
            strings(&["-Zno_trust_verify=off"]),
            strings(&["-Ztrust-verify-session=forged"]),
            strings(&["-Ztrust-verify-crate-role=primary"]),
            strings(&["-Ztrust-policy=certify", "-Ztrust_policy=certify"]),
            strings(&["-Ztrust-verify=on", "-Ztrust_verify=true"]),
        ] {
            reconcile_overridden_config_trust_policy(&configured, &policy)
                .expect_err("discarded configuration cannot grant competing authority");
        }
        reconcile_overridden_config_trust_policy(
            &strings(&["-Ztrust-policy=certify"]),
            &strings(&["-Ztrust-policy=certify"]),
        )
        .expect_err("matching values without the authenticated protocol cannot enter a Unit");
    }

    #[test]
    fn typed_boolean_and_level_aliases_match_imported_policy_without_activation() {
        let imported = strings(&[
            "-Ztrust-verify-session=typed-policy",
            "-Ztrust-proof-artifact-root=/tmp/typed-policy",
            "-Ztrust-verify-include-dependencies=yes",
            "-Ztrust-verify-level=2",
            "-Ztrust-ir-lower=on",
        ]);
        assert!(
            reconcile_overridden_config_trust_policy(
                &strings(&[
                    "-Ztrust_verify_include_dependencies=true",
                    "-Ztrust_verify_level=02",
                    "-Ztrust_ir_lower=yes"
                ]),
                &imported,
            )
            .unwrap()
            .is_empty()
        );
        assert!(
            reconcile_overridden_config_trust_policy(
                &strings(&["-Ztrust_verify_include_dependencies=false"]),
                &imported,
            )
            .is_err()
        );
    }

    #[test]
    fn overridden_codegen_flags_keep_ordinary_environment_precedence() {
        assert!(
            reconcile_overridden_config_trust_policy(
                &strings(&["-Ctarget-cpu=native", "-Coverflow-checks=off"]),
                &[],
            )
            .unwrap()
            .is_empty()
        );
        reconcile_overridden_config_trust_policy(&strings(&["-Zcontract_checks=off"]), &[])
            .expect_err("retired exec projections cannot be hidden in overridden configuration");
    }

    fn verified_lane(extra: &[&str]) -> TrustLane {
        let mut lane = strings(&[
            "-Ztrust-verify-session=proof-trust-cg",
            "-Ztrust-proof-artifact-root=/tmp/proof-trust-cg",
        ]);
        lane.extend(strings(extra));
        TrustLane::new(true, false, Flags::Rust, Some(lane)).expect("a verified lane")
    }

    fn host(flags: &[&str]) -> Option<FlagSource> {
        Some(FlagSource {
            origin: "/ws/.cargo/config.toml (`[host]` rustflags)".to_string(),
            flags: strings(flags),
        })
    }

    #[test]
    fn trust_cg_target_forces_host_only_units_to_llvm() {
        let target = strings(&[
            "-Cpanic=abort",
            "-Cdebuginfo=0",
            "-Ccodegen-units=1",
            "-Zcodegen-backend=trust-cg",
            "-Ztrust-verify-session=proof-trust-cg",
        ]);
        assert_eq!(
            verified_targo_target_codegen_backend(&target)
                .unwrap()
                .as_deref(),
            Some("trust-cg")
        );

        let lane = verified_lane(&[
            "-Zcodegen-backend=trust-cg",
            "-Cpanic=abort",
            "-Cdebuginfo=0",
            "-Ccodegen-units=1",
        ]);
        for host_backend in ["-Zcodegen-backend=llvm", "-Zcodegen_backend=llvm"] {
            let mut notices = Vec::new();
            let host_flags = lane
                .host_flags(host(&["-Cdebuginfo=2", host_backend]), &mut notices)
                .expect("a host backend is dropped, not refused");
            // The host artifact keeps its own debuginfo (trust-cg's contract
            // is the target's), takes LLVM, then the lane's host policy.
            assert_eq!(
                host_flags,
                strings(&[
                    "-Cdebuginfo=2",
                    "-Z",
                    "codegen-backend=llvm",
                    "-Ztrust-verify-session=proof-trust-cg",
                    "-Ztrust-proof-artifact-root=/tmp/proof-trust-cg",
                ])
            );
            assert!(
                !host_flags
                    .iter()
                    .any(|arg| arg.contains("codegen-backend=trust"))
            );
            assert_eq!(notices.len(), 1, "{notices:?}");
            assert!(notices[0].contains(host_backend), "{notices:?}");
            assert!(notices[0].contains("`[host]` rustflags"), "{notices:?}");
        }
    }

    // Trust (T14-APPEND-2): a competing `[host]` backend used to refuse the
    // run; like every other lane-owned option it is now dropped and named,
    // and the host artifact still compiles through LLVM.
    #[test]
    fn trust_cg_target_drops_and_names_a_competing_host_codegen_backend() {
        let lane = verified_lane(&["-Zcodegen-backend=trust-cg"]);
        for host_flags in [
            &["-Zcodegen-backend=cranelift"][..],
            &["-Z", "codegen-backend=trust-cg"][..],
            &["-Zcodegen_backend=trust-cg"][..],
            &["-Zcodegen-backend"][..],
        ] {
            let mut notices = Vec::new();
            let resolved = lane
                .host_flags(host(host_flags), &mut notices)
                .expect("a lane-owned host option is dropped, not refused");
            assert_eq!(
                resolved
                    .windows(2)
                    .filter(|pair| pair[0] == "-Z" && pair[1].starts_with("codegen-backend"))
                    .map(|pair| pair[1].as_str())
                    .collect::<Vec<_>>(),
                ["codegen-backend=llvm"],
                "{resolved:?}"
            );
            assert!(
                !resolved
                    .iter()
                    .any(|arg| arg.contains("cranelift") || arg == "-Zcodegen-backend"),
                "{resolved:?}"
            );
            assert_eq!(notices.len(), 1, "{notices:?}");
        }
    }

    #[test]
    fn verified_targo_target_backend_parser_is_exact_and_rejects_duplicates() {
        assert_eq!(
            verified_targo_target_codegen_backend(&strings(&[
                "-Z",
                "codegen-backend=llvm",
                "-Ztrust-verify-session=proof",
            ]))
            .unwrap()
            .as_deref(),
            Some("llvm")
        );
        assert!(
            verified_targo_target_codegen_backend(&strings(&[
                "-Zcodegen-backend=llvm",
                "-Z",
                "codegen-backend=trust-cg",
            ]))
            .is_err()
        );
        assert!(verified_targo_target_codegen_backend(&strings(&["-Zcodegen-backend="])).is_err());
        assert_eq!(
            verified_targo_target_codegen_backend(&strings(&["-Zcodegen_backend=trust-cg",]))
                .unwrap()
                .as_deref(),
            Some("trust-cg")
        );
        assert_eq!(
            verified_targo_target_codegen_backend(&strings(&["-Zcodegen-backend=trust_cg",]))
                .unwrap()
                .as_deref(),
            Some("trust-cg")
        );
        assert!(
            verified_targo_target_codegen_backend(&strings(&[
                "-Zcodegen-backend=llvm",
                "-Zcodegen_backend=trust-cg",
            ]))
            .is_err(),
            "rustc-equivalent backend keys must be duplicate policy"
        );
    }

    #[test]
    fn rustc_equivalent_z_and_c_keys_cannot_bypass_verified_host_policy() {
        let policy = extract_verified_targo_host_policy(&strings(&[
            "-Coverflow_checks=yes",
            "-C",
            "debug_assertions=yes",
            "-Ztrust_verify_level=2",
            "-Ztrust_verify-session=proof-equivalent",
            "-Ztrust-proof_artifact_root=/tmp/proof-equivalent",
        ]))
        .expect("rustc-equivalent keys are the same verified policy");
        assert!(policy.iter().any(|arg| arg.contains("overflow_checks")));
        assert!(policy.iter().any(|arg| arg.contains("debug_assertions")));
        assert!(policy.iter().any(|arg| arg.contains("trust_verify_level")));

        let duplicate_session = extract_verified_targo_host_policy(&strings(&[
            "-Ztrust-verify-session=one",
            "-Ztrust_verify_session=two",
            "-Ztrust-proof-artifact-root=/tmp/proof-equivalent",
        ]))
        .expect_err("alternate key spelling must not evade duplicate detection");
        assert!(duplicate_session.to_string().contains("duplicate"));

        let reserved = extract_verified_targo_host_policy(&strings(&[
            "-Ztrust_verify_session=proof",
            "-Ztrust_proof_artifact_root=/tmp/proof-equivalent",
            "-Ztrust_verify_crate_role=primary",
        ]))
        .expect_err("alternate key spelling must not evade reserved metadata");
        assert!(reserved.to_string().contains("reserved for Targo"));

        for host_flag in ["-Coverflow_checks=no", "-Cdebug_assertions=no"] {
            let error = reconcile_host_config_trust_policy(&strings(&[host_flag]), &policy)
                .expect_err("alternate -C key must not compete with imported safety policy");
            assert!(error.to_string().contains("cannot set -C"), "{error:#}");
        }
    }

    #[test]
    fn strict_safety_policy_crosses_the_host_boundary_without_competing_host_flags() {
        let policy = extract_verified_targo_host_policy(&strings(&[
            "-C",
            "overflow-checks=yes",
            "-Cdebug-assertions=yes",
            "-Ztrust-verify-session=proof-safety",
            "-Ztrust-proof-artifact-root=/tmp/trust-proof-safety",
        ]))
        .expect("valid strict host policy");
        assert_eq!(
            policy,
            strings(&[
                "-C",
                "overflow-checks=yes",
                "-Cdebug-assertions=yes",
                "-Ztrust-verify-session=proof-safety",
                "-Ztrust-proof-artifact-root=/tmp/trust-proof-safety",
            ])
        );

        for host_flag in ["-Coverflow-checks=no", "-Cdebug-assertions=no"] {
            let error = reconcile_host_config_trust_policy(&strings(&[host_flag]), &policy)
                .expect_err("host config must not compete with imported proof safety policy");
            assert!(error.to_string().contains("cannot set -C"), "{error:#}");
        }
        reconcile_host_config_trust_policy(&strings(&["-Ctarget-cpu=native"]), &policy)
            .expect("unrelated host codegen policy remains supported");
    }

    #[test]
    fn malformed_or_duplicate_host_safety_policy_fails_closed() {
        for rustflags in [
            strings(&["-Coverflow-checks=maybe", "-Ztrust-verify-session=proof"]),
            strings(&["-Cdebug-assertions=no", "-Ztrust-verify-session=proof"]),
            strings(&[
                "-Coverflow-checks=yes",
                "-C",
                "overflow-checks=yes",
                "-Ztrust-verify-session=proof",
            ]),
        ] {
            assert!(extract_verified_targo_host_policy(&rustflags).is_err());
        }
    }

    #[test]
    fn host_policy_session_changes_are_visible_before_unit_fingerprinting() {
        let lane = |encoded: &str| {
            TrustLane::new(
                true,
                false,
                Flags::Rust,
                decode_lane_rustflags(Some(OsStr::new(encoded))).unwrap(),
            )
            .unwrap()
            .host_policy
        };
        let first = lane(
            "-Z\x1ftrust-verify-session=proof-1\x1f-Z\x1ftrust-proof-artifact-root=/tmp/proof-1",
        );
        let second = lane(
            "-Z\x1ftrust-verify-session=proof-2\x1f-Z\x1ftrust-proof-artifact-root=/tmp/proof-2",
        );
        // This vector becomes TargetInfo::rustflags and then Unit::rustflags,
        // which Cargo includes verbatim in the Fingerprint.
        assert_ne!(first, second);
        assert!(first.iter().any(|arg| arg.ends_with("proof-1")));
        assert!(second.iter().any(|arg| arg.ends_with("proof-2")));
    }

    #[test]
    fn verified_host_policy_requires_one_absolute_proof_artifact_root() {
        let missing =
            extract_verified_targo_host_policy(&strings(&["-Ztrust-verify-session=proof"]))
                .expect_err(
                    "verified host policy must never fall back to Cargo's working directory",
                );
        assert!(missing.to_string().contains("trust-proof-artifact-root"));

        for malformed in [
            strings(&[
                "-Ztrust-verify-session=proof",
                "-Ztrust-proof-artifact-root=relative",
            ]),
            strings(&[
                "-Ztrust-verify-session=proof",
                "-Ztrust-proof-artifact-root=/tmp/one",
                "-Ztrust-proof-artifact-root=/tmp/two",
            ]),
        ] {
            assert!(extract_verified_targo_host_policy(&malformed).is_err());
        }
    }

    #[test]
    fn ordinary_cargo_keeps_cross_target_host_rustflags_isolated() {
        // Ordinary Cargo never decodes the lane (`TrustLane::current` reads it
        // only in a branded invocation), and a lane-less state imports nothing
        // across the host boundary.
        let lane = TrustLane::new(false, false, Flags::Rust, None).unwrap();
        assert!(lane.rustflags.is_none());
        assert!(lane.host_policy.is_empty());
    }

    #[test]
    fn caller_cannot_supply_cargo_owned_unit_metadata() {
        let error = extract_verified_targo_host_policy(&strings(&[
            "-Ztrust-verify-session=proof",
            "-Ztrust-verify-crate-role=primary",
        ]))
        .unwrap_err();
        assert!(
            error.to_string().contains("reserved for Targo"),
            "{error:#}"
        );
    }

    #[cfg(unix)]
    #[test]
    fn a_non_unicode_lane_is_refused() {
        use std::os::unix::ffi::OsStringExt;

        let invalid = std::ffi::OsString::from_vec(vec![0xff, 0xfe]);
        let error = decode_lane_rustflags(Some(&invalid)).unwrap_err();
        assert!(error.to_string().contains("not valid Unicode"), "{error:#}");
        assert_eq!(decode_lane_rustflags(None).unwrap(), None);
        assert_eq!(
            decode_lane_rustflags(Some(OsStr::new(""))).unwrap(),
            Some(Vec::new())
        );
    }
}

// Trust (T14a, DECISION_QUEUE T14-APPEND-1/2): `extra_args` over a real
// `GlobalContext` and its configuration. The frontend brand and the verified
// marker are process-wide, so the lane state is handed in (`TrustLane::new`
// is what `TrustLane::current` builds from them).
#[cfg(test)]
mod lane_inheritance_tests {
    use std::str::FromStr;

    use cargo_platform::Cfg;

    use super::{
        FlagSource, Flags, LaneOwnership, TargetInfo, TargetInfoProbeLane, TrustLane,
        drop_lane_owned_options, extra_args_in_lane, reports_trust_verify, target_info_probe_flags,
        trust_verify_default_query_flags, trust_verify_default_query_process,
    };
    use crate::compiler::{CompileKind, CompileTarget};
    use crate::util::GlobalContext;
    use crate::util::data_structures::HashMap;

    const HOST: &str = "aarch64-apple-darwin";

    fn strings(values: &[&str]) -> Vec<String> {
        values.iter().map(|value| (*value).to_string()).collect()
    }

    fn context(
        config: &str,
        env: &[(&str, &str)],
        host_config: bool,
    ) -> (tempfile::TempDir, GlobalContext) {
        let temp = tempfile::tempdir().unwrap();
        std::fs::create_dir(temp.path().join(".cargo")).unwrap();
        std::fs::write(temp.path().join(".cargo/config.toml"), config).unwrap();
        let mut gctx = GlobalContext::new(
            cargo_util_terminal::Shell::new(),
            temp.path().to_path_buf(),
            temp.path().join("home"),
        );
        gctx.set_search_stop_path(temp.path().to_path_buf());
        gctx.set_env(
            env.iter()
                .map(|(name, value)| (name.to_string(), value.to_string()))
                .collect::<HashMap<_, _>>(),
        );
        gctx.nightly_features_allowed = true;
        let unstable = if host_config {
            strings(&["host-config", "target-applies-to-host"])
        } else {
            Vec::new()
        };
        gctx.configure(0, false, None, false, false, true, &None, &unstable, &[])
            .unwrap();
        (temp, gctx)
    }

    /// The lane `targo trust` hands Cargo: a level, the strict safety checks,
    /// the session and the proof root.
    fn verified_lane_flags() -> Vec<String> {
        strings(&[
            "-Z",
            "trust-verify-level=2",
            "-Z",
            "codegen-backend=llvm",
            "-C",
            "overflow-checks=yes",
            "-C",
            "debug-assertions=yes",
            "-Z",
            "trust-verify-session=t14",
            "-Z",
            "trust-proof-artifact-root=/tmp/t14-proof",
        ])
    }

    fn verified_lane() -> TrustLane {
        TrustLane::new(true, false, Flags::Rust, Some(verified_lane_flags())).unwrap()
    }

    fn cfg() -> Vec<Cfg> {
        ["unix", "trust_verify"]
            .into_iter()
            .map(|cfg| Cfg::from_str(cfg).unwrap())
            .collect()
    }

    fn resolve(
        gctx: &GlobalContext,
        lane: &TrustLane,
    ) -> anyhow::Result<(Vec<String>, Vec<String>)> {
        extra_args_in_lane(
            gctx,
            &[CompileKind::Host],
            HOST,
            Some(&cfg()),
            CompileKind::Host,
            Flags::Rust,
            lane,
        )
    }

    const ATERM_TABLE: &str = r#"
[target.'cfg(trust_verify)']
rustflags = ["--cfg", "clean_islands", "-Zthreads=4"]
"#;

    #[test]
    fn the_cfg_table_comes_first_and_the_lane_last() {
        let (_temp, gctx) = context(ATERM_TABLE, &[], false);
        let (args, notices) = resolve(&gctx, &verified_lane()).unwrap();
        let mut expected = strings(&["--cfg", "clean_islands", "-Zthreads=4"]);
        expected.extend(verified_lane_flags());
        assert_eq!(args, expected);
        assert!(notices.is_empty(), "{notices:?}");
    }

    #[test]
    fn environment_rustflags_win_over_the_table_and_the_lane_is_still_appended() {
        for (name, value) in [
            ("RUSTFLAGS", "-Copt-level=1 -Ztrust-policy=advisory"),
            (
                "CARGO_ENCODED_RUSTFLAGS",
                "-Copt-level=1\x1f-Z\x1ftrust_policy=advisory",
            ),
        ] {
            let (_temp, gctx) = context(ATERM_TABLE, &[(name, value)], false);
            let (args, notices) = resolve(&gctx, &verified_lane()).unwrap();
            // Cargo's precedence: the environment replaces the table. Its
            // `-Ztrust-*` token is dropped (targo trust names it), and the lane
            // comes last.
            let mut expected = strings(&["-Copt-level=1"]);
            expected.extend(verified_lane_flags());
            assert_eq!(args, expected, "{name}");
            // The replaced table is named, so a committed `--cfg` never
            // leaves the proof set silently.
            assert_eq!(notices.len(), 1, "{notices:?}");
            assert!(notices[0].contains(&format!("`{name}`")), "{}", notices[0]);
            assert!(
                notices[0].contains("`target.'cfg(trust_verify)'.rustflags`"),
                "{}",
                notices[0]
            );
        }

        // An empty `CARGO_ENCODED_RUSTFLAGS` (some harnesses export one)
        // replaces the table too, and is named the same way.
        let (_temp, gctx) = context(ATERM_TABLE, &[("CARGO_ENCODED_RUSTFLAGS", "")], false);
        let (args, notices) = resolve(&gctx, &verified_lane()).unwrap();
        assert_eq!(args, verified_lane_flags());
        assert_eq!(notices.len(), 1, "{notices:?}");
        assert!(
            notices[0].contains("none of them reach this build"),
            "{}",
            notices[0]
        );

        // With nothing configured there is nothing to name.
        let (_temp, gctx) = context("", &[("RUSTFLAGS", "-Copt-level=1")], false);
        let (_, notices) = resolve(&gctx, &verified_lane()).unwrap();
        assert!(notices.is_empty(), "{notices:?}");
    }

    #[test]
    fn a_configured_off_switch_is_refused() {
        for config in [
            "[build]\nrustflags = [\"-Ztrust-verify=off\"]\n",
            "[target.'cfg(trust_verify)']\nrustflags = [\"-Z\", \"trust_verify=off\"]\n",
        ] {
            let (_temp, gctx) = context(config, &[], false);
            let error = resolve(&gctx, &verified_lane()).unwrap_err();
            assert!(
                format!("{error:#}").contains("-Ztrust-verify is reserved"),
                "{error:#}"
            );
        }
    }

    #[test]
    fn a_configured_trust_policy_matches_the_lane_or_refuses() {
        let mut lane_flags = verified_lane_flags();
        lane_flags.extend(strings(&["-Z", "trust-policy=certify"]));
        let lane = TrustLane::new(true, false, Flags::Rust, Some(lane_flags.clone())).unwrap();

        let (_temp, gctx) = context(
            "[target.'cfg(trust_verify)']\nrustflags = [\"--cfg\", \"kept\", \"-Ztrust-policy=certify\"]\n",
            &[],
            false,
        );
        let (args, notices) = resolve(&gctx, &lane).unwrap();
        // The assertion is checked and the lane carries the policy once.
        let mut expected = strings(&["--cfg", "kept"]);
        expected.extend(lane_flags);
        assert_eq!(args, expected);
        assert!(notices.is_empty(), "{notices:?}");

        let (_temp, gctx) = context(
            "[target.'cfg(trust_verify)']\nrustflags = [\"-Ztrust-policy=advisory\"]\n",
            &[],
            false,
        );
        let error = resolve(&gctx, &lane).unwrap_err();
        assert!(
            format!("{error:#}").contains("configured policy assertion -Ztrust_policy=advisory"),
            "{error:#}"
        );

        // The environment winning does not exempt the configured assertion.
        let (_temp, gctx) = context(
            "[target.'cfg(trust_verify)']\nrustflags = [\"-Ztrust-policy=advisory\"]\n",
            &[("RUSTFLAGS", "-Copt-level=1")],
            false,
        );
        assert!(resolve(&gctx, &lane).is_err());
    }

    #[test]
    fn lane_owned_options_are_dropped_with_a_notice_naming_their_file() {
        let (temp, gctx) = context(
            r#"
[build]
rustflags = [
    "-Zcodegen-backend=/abs/librustc_codegen_trust_mc.dylib",
    "-C", "llvm-args=-inline-threshold=0",
    "-Coverflow-checks=no",
    "--cfg", "kept",
    "-Zllvm-plugins=/abs/plugin.dylib",
]
"#,
            &[],
            false,
        );
        let (args, notices) = resolve(&gctx, &verified_lane()).unwrap();
        let mut expected = strings(&["--cfg", "kept"]);
        expected.extend(verified_lane_flags());
        assert_eq!(args, expected);
        assert_eq!(notices.len(), 4, "{notices:?}");
        let config = temp.path().join(".cargo/config.toml");
        for (notice, option) in notices.iter().zip([
            "-Zcodegen-backend=/abs/librustc_codegen_trust_mc.dylib",
            "-C llvm-args=-inline-threshold=0",
            "-Coverflow-checks=no",
            "-Zllvm-plugins=/abs/plugin.dylib",
        ]) {
            assert!(notice.contains(&format!("`{option}`")), "{notice}");
            assert!(notice.contains(&config.display().to_string()), "{notice}");
            assert!(notice.contains("`build.rustflags`"), "{notice}");
        }
    }

    /// An argument file hides its flags from the lane-owned classifier, so a
    /// `-Zcodegen-backend` inside one would load into a probe's compiler; a
    /// `--` would put the lane's flags behind rustc's last option. Both are
    /// refused from every project source, under the verified lane and under
    /// a probe's empty lane, naming the source.
    #[test]
    fn argument_files_and_separators_are_refused_from_every_project_source() {
        let probe_lane = TrustLane::new(false, false, Flags::Rust, Some(Vec::new())).unwrap();
        for lane in [verified_lane(), probe_lane] {
            let (temp, gctx) = context(
                "[build]\nrustflags = [\"--cfg\", \"kept\", \"@forged.args\"]\n",
                &[],
                false,
            );
            let error = resolve(&gctx, &lane).unwrap_err().to_string();
            assert!(error.contains("`@forged.args`"), "{error}");
            assert!(error.contains("argument file"), "{error}");
            let config = temp.path().join(".cargo/config.toml");
            assert!(error.contains(&config.display().to_string()), "{error}");

            let (_temp, gctx) = context(
                ATERM_TABLE,
                &[("CARGO_ENCODED_RUSTFLAGS", "--cfg\x1fenv\x1f@argv.txt")],
                false,
            );
            let error = resolve(&gctx, &lane).unwrap_err().to_string();
            assert!(error.contains("`@argv.txt`"), "{error}");
            assert!(error.contains("`CARGO_ENCODED_RUSTFLAGS`"), "{error}");

            let (_temp, gctx) = context(
                "[target.'cfg(trust_verify)']\nrustflags = [\"--\", \"-Ztrust-verify=off\"]\n",
                &[],
                false,
            );
            let error = resolve(&gctx, &lane).unwrap_err().to_string();
            assert!(error.contains("`--`"), "{error}");
            assert!(error.contains("ends rustc's options"), "{error}");

            let (_temp, gctx) = context("[host]\nrustflags = [\"@host.args\"]\n", &[], true);
            let requested = [CompileKind::Target(
                CompileTarget::new("aarch64-unknown-linux-gnu", false).unwrap(),
            )];
            let error = extra_args_in_lane(
                &gctx,
                &requested,
                HOST,
                Some(&cfg()),
                CompileKind::Host,
                Flags::Rust,
                &lane,
            )
            .unwrap_err()
            .to_string();
            assert!(error.contains("`@host.args`"), "{error}");
            assert!(error.contains("`[host]` rustflags"), "{error}");
        }

        // Ordinary Cargo (no lane) keeps upstream's behavior: rustc expands
        // the file, and nothing here reads it.
        let (_temp, gctx) = context("[build]\nrustflags = [\"@forged.args\"]\n", &[], false);
        let no_lane = TrustLane::new(false, false, Flags::Rust, None).unwrap();
        let (args, _) = resolve(&gctx, &no_lane).unwrap();
        assert_eq!(args, strings(&["@forged.args"]));

        // The lane itself is held to the same rule.
        assert!(TrustLane::new(false, false, Flags::Rust, Some(strings(&["@lane.args"]))).is_err());
        // Outside the verified lane it carries only the probe contract, so a
        // hand-set value is no second ambient rustflags channel.
        for allowed in [
            strings(&[
                "-C",
                "panic=abort",
                "-Cdebuginfo=0",
                "--codegen=codegen-units=1",
            ]),
            strings(&[
                "--codegen",
                "overflow-checks=yes",
                "-C",
                "debug-assertions=yes",
            ]),
        ] {
            assert!(TrustLane::new(false, true, Flags::Rust, Some(allowed)).is_ok());
        }
        for refused in [
            strings(&["--cfg", "stray"]),
            strings(&["-Copt-level=3"]),
            strings(&["-Zcodegen-backend=/abs/backend.dylib"]),
        ] {
            let error = TrustLane::new(false, true, Flags::Rust, Some(refused.clone()))
                .unwrap_err()
                .to_string();
            assert!(error.contains("probe contract"), "{refused:?}: {error}");
        }
        assert!(TrustLane::new(false, false, Flags::Rust, Some(strings(&["--"]))).is_err());
    }

    #[test]
    fn a_lane_without_the_strict_checks_leaves_the_projects_safety_options() {
        let (_temp, gctx) = context(
            "[build]\nrustflags = [\"-Coverflow-checks=no\"]\n",
            &[],
            false,
        );
        let lane = strings(&[
            "-Z",
            "trust-verify-session=t14",
            "-Z",
            "trust-proof-artifact-root=/tmp/t14-proof",
        ]);
        let lane_state = TrustLane::new(true, false, Flags::Rust, Some(lane.clone())).unwrap();
        let (args, notices) = resolve(&gctx, &lane_state).unwrap();
        let mut expected = strings(&["-Coverflow-checks=no"]);
        expected.extend(lane);
        assert_eq!(args, expected);
        assert!(notices.is_empty(), "{notices:?}");
    }

    #[test]
    fn the_lane_needs_the_verified_marker_and_the_marker_needs_a_session() {
        // Trust tokens in the lane without TRUST_TARGO_VERIFY=1.
        for lane in [
            strings(&["-Ztrust-policy=certify"]),
            strings(&["-Z", "trust_verify_level=2"]),
            strings(&["-Zno-trust-verify=yes"]),
        ] {
            let error = TrustLane::new(false, true, Flags::Rust, Some(lane)).unwrap_err();
            assert!(
                error.to_string().contains("without TRUST_TARGO_VERIFY=1"),
                "{error:#}"
            );
        }
        // The marker without a session or a proof root, or without a lane.
        for lane in [
            Some(strings(&["-Ztrust-verify-level=2"])),
            Some(strings(&["-Ztrust-verify-session=t14"])),
            None,
        ] {
            assert!(TrustLane::new(true, false, Flags::Rust, lane).is_err());
        }
        // The off-switch is never part of a lane.
        let mut lane = verified_lane_flags();
        lane.push("-Ztrust-verify=off".to_string());
        assert!(TrustLane::new(true, false, Flags::Rust, Some(lane)).is_err());
        // A rustdoc invocation of the verified lane reads no lane.
        let rustdoc = TrustLane::new(true, false, Flags::Rustdoc, None).unwrap();
        assert!(rustdoc.rustflags.is_none());
    }

    /// The selection probes run in the unverified lane with a lane that
    /// carries no Trust option: configured and environment flags reach them
    /// as they reach the build, minus an external backend, which never loads
    /// into a probe's compiler (S9).
    #[test]
    fn a_probe_lane_drops_an_external_backend_from_every_channel() {
        let probe_lane = strings(&[
            "-C",
            "panic=abort",
            "-C",
            "debuginfo=0",
            "-C",
            "codegen-units=1",
        ]);
        let lane = TrustLane::new(false, true, Flags::Rust, Some(probe_lane.clone())).unwrap();

        let (_temp, gctx) = context(
            "[build]\nrustflags = [\"-Zcodegen-backend=/abs/trust_mc.dylib\", \"--cfg\", \"configured\"]\n",
            &[],
            false,
        );
        let (args, notices) = resolve(&gctx, &lane).unwrap();
        let mut expected = strings(&["--cfg", "configured"]);
        expected.extend(probe_lane.clone());
        expected.push("-Ztrust-verify=off".to_string());
        assert_eq!(args, expected);
        assert_eq!(notices.len(), 1, "{notices:?}");

        let (_temp, gctx) = context(
            "",
            &[(
                "CARGO_ENCODED_RUSTFLAGS",
                "-Z\x1fcodegen-backend=/abs/trust_mc.dylib\x1f--cfg\x1fprobe_cfg\x1f-Cpanic=unwind\x1f-g",
            )],
            false,
        );
        let (args, notices) = resolve(&gctx, &lane).unwrap();
        let mut expected = strings(&["--cfg", "probe_cfg"]);
        expected.extend(probe_lane);
        expected.push("-Ztrust-verify=off".to_string());
        assert_eq!(args, expected);
        assert_eq!(notices.len(), 3, "{notices:?}");
        assert!(
            notices
                .iter()
                .all(|notice| notice.contains("environment variable `CARGO_ENCODED_RUSTFLAGS`")),
            "{notices:?}"
        );

        // An empty lane still owns the backend.
        let empty = TrustLane::new(false, true, Flags::Rust, Some(Vec::new())).unwrap();
        let (_temp, gctx) = context(
            "",
            &[("RUSTFLAGS", "-Zcodegen-backend=/abs/x.dylib")],
            false,
        );
        let (args, _) = resolve(&gctx, &empty).unwrap();
        assert_eq!(args, strings(&["-Ztrust-verify=off"]));
    }

    #[test]
    fn without_a_lane_nothing_changes() {
        let (_temp, gctx) = context(ATERM_TABLE, &[], false);
        let unverified = TrustLane::new(false, true, Flags::Rust, None).unwrap();
        let (args, notices) = resolve(&gctx, &unverified).unwrap();
        assert_eq!(
            args,
            strings(&[
                "--cfg",
                "clean_islands",
                "-Zthreads=4",
                "-Ztrust-verify=off"
            ])
        );
        assert!(notices.is_empty());
    }

    #[test]
    fn an_isolated_host_artifact_takes_host_flags_and_the_lane_host_policy() {
        let (temp, gctx) = context(
            r#"
[host]
rustflags = ["--cfg", "host_cfg", "-Cllvm-args=-x", "-Cdebug-assertions=off"]
[target.'cfg(trust_verify)']
rustflags = ["--cfg", "target_only"]
"#,
            &[],
            true,
        );
        let requested = [CompileKind::Target(
            CompileTarget::new("aarch64-unknown-linux-gnu", false).unwrap(),
        )];
        let (args, notices) = extra_args_in_lane(
            &gctx,
            &requested,
            HOST,
            Some(&cfg()),
            CompileKind::Host,
            Flags::Rust,
            &verified_lane(),
        )
        .unwrap();
        // `[host]` alone, minus what the lane owns, then the lane's host policy
        // (the backend is not part of it; the safety checks are).
        assert_eq!(
            args,
            strings(&[
                "--cfg",
                "host_cfg",
                "-Z",
                "trust-verify-level=2",
                "-C",
                "overflow-checks=yes",
                "-C",
                "debug-assertions=yes",
                "-Z",
                "trust-verify-session=t14",
                "-Z",
                "trust-proof-artifact-root=/tmp/t14-proof",
            ])
        );
        assert_eq!(notices.len(), 2, "{notices:?}");
        let config = temp.path().join(".cargo/config.toml");
        assert!(
            notices
                .iter()
                .all(|notice| notice.contains(&config.display().to_string())),
            "{notices:?}"
        );
    }

    /// The classifier reads every spelling rustc accepts: `-C x`, `-Cx`,
    /// `--codegen x`, `--codegen=x`, `-`/`_` in names, and `-g`. This is the
    /// coverage targo-trust's inherited-flag sanitizer carried before T14a
    /// moved the classifier here.
    #[test]
    fn the_classifier_reads_every_option_spelling_and_names_each_drop() {
        let source = |flags: Vec<&str>| FlagSource {
            origin: "`test`".to_string(),
            flags: strings(&flags),
        };
        let none = LaneOwnership::default();
        let safety = LaneOwnership {
            safety_checks: true,
            trust_cg_contract: false,
        };
        let contract = LaneOwnership {
            safety_checks: false,
            trust_cg_contract: true,
        };
        let both = LaneOwnership {
            safety_checks: true,
            trust_cg_contract: true,
        };

        // Always the lane's: the backend, LLVM plugins and LLVM arguments.
        for spelling in [
            vec!["-Zcodegen-backend=/abs/librustc_codegen_trust_mc.dylib"],
            vec!["-Zcodegen_backend=trust_mc"],
            vec!["-Z", "codegen-backend=trust-mc"],
            vec!["-Zllvm-plugins=/tmp/forged.dylib"],
            vec!["-Z", "llvm_plugins=/tmp/forged.dylib"],
            vec!["-Cllvm-args=--reachability=harnesses"],
            vec!["-C", "llvm-args=--ay-chc"],
            vec!["-Cllvm_args=-load=/tmp/forged.dylib"],
            vec!["-C", "llvm_args=x"],
            vec!["--codegen=llvm_args=-load=/tmp/forged.dylib"],
            vec!["--codegen", "llvm-args=-load=/tmp/forged.dylib"],
        ] {
            let mut flags = spelling.clone();
            flags.extend(["-Copt-level=2", "--cfg", "kani"]);
            for ownership in [none, safety, contract, both] {
                let mut notices = Vec::new();
                assert_eq!(
                    drop_lane_owned_options(&source(flags.clone()), ownership, &mut notices),
                    strings(&["-Copt-level=2", "--cfg", "kani"]),
                    "{spelling:?} survived under {ownership:?}"
                );
                assert_eq!(notices.len(), 1, "{notices:?}");
                assert!(notices[0].contains(&spelling.join(" ")), "{notices:?}");
                assert!(notices[0].contains("`test`"), "{notices:?}");
            }
        }

        // The strict safety checks, only when the lane forces them.
        let overrides = vec![
            "-Coverflow-checks=no",
            "-C",
            "debug-assertions=off",
            "--codegen=overflow_checks=no",
            "--codegen",
            "debug_assertions=off",
            "-Copt-level=2",
        ];
        for ownership in [safety, both] {
            let mut notices = Vec::new();
            assert_eq!(
                drop_lane_owned_options(&source(overrides.clone()), ownership, &mut notices),
                strings(&["-Copt-level=2"])
            );
            assert_eq!(notices.len(), 4, "{notices:?}");
        }
        for ownership in [none, contract] {
            let mut notices = Vec::new();
            assert_eq!(
                drop_lane_owned_options(&source(overrides.clone()), ownership, &mut notices),
                strings(&overrides),
                "an advisory lane keeps the project's profile fidelity"
            );
            assert!(notices.is_empty());
        }

        // trust-cg's codegen contract, only when the lane carries it.
        let contract_overrides = vec![
            "-g",
            "-Cpanic=unwind",
            "-C",
            "debuginfo=2",
            "-Ccodegen-units=16",
            "-C",
            "incremental=/tmp/hostile",
            "--codegen=incremental=/tmp/hostile-long",
            "--codegen",
            "codegen_units=32",
            "-Copt-level=3",
        ];
        for ownership in [contract, both] {
            let mut notices = Vec::new();
            assert_eq!(
                drop_lane_owned_options(
                    &source(contract_overrides.clone()),
                    ownership,
                    &mut notices
                ),
                strings(&["-Copt-level=3"])
            );
            assert_eq!(notices.len(), 7, "{notices:?}");
        }
        let mut notices = Vec::new();
        assert_eq!(
            drop_lane_owned_options(&source(contract_overrides.clone()), safety, &mut notices),
            strings(&contract_overrides)
        );

        // A `-C` metadata value that merely mentions an owned name is kept.
        let mut notices = Vec::new();
        assert_eq!(
            drop_lane_owned_options(
                &source(vec![
                    "-C",
                    "metadata=overflow-checks=no",
                    "--cfg",
                    "llvm_args"
                ]),
                both,
                &mut notices
            ),
            strings(&["-C", "metadata=overflow-checks=no", "--cfg", "llvm_args"])
        );
        assert!(notices.is_empty());
    }

    #[test]
    fn lane_ownership_is_read_from_the_lane_itself() {
        let lane = strings(&[
            "-Z",
            "codegen-backend=trust-cg",
            "-C",
            "panic=abort",
            "--codegen=overflow_checks=yes",
        ]);
        assert_eq!(
            LaneOwnership::of(&lane).unwrap(),
            LaneOwnership {
                safety_checks: true,
                trust_cg_contract: true,
            }
        );
        assert_eq!(
            LaneOwnership::of(&strings(&["-Z", "trust-verify-level=2"])).unwrap(),
            LaneOwnership::default()
        );
    }

    /// T14b: in a branded invocation the target-info probe runs the selected
    /// compiler, so `targo tippy` (tippy-driver as `RUSTC_WORKSPACE_WRAPPER`)
    /// matches the `cfg(trust_verify)` table as `targo --unverified check`
    /// does. Ordinary Cargo still probes through the workspace wrapper.
    #[cfg(unix)]
    #[test]
    fn a_branded_target_info_probe_skips_the_workspace_wrapper() {
        use std::os::unix::fs::PermissionsExt as _;

        let (temp, gctx) = context("", &[], false);
        let script = |name: &str, body: &str| {
            let path = temp.path().join(name);
            std::fs::write(&path, format!("#!/bin/sh\n{body}\n")).unwrap();
            let mut permissions = std::fs::metadata(&path).unwrap().permissions();
            permissions.set_mode(0o755);
            std::fs::set_permissions(&path, permissions).unwrap();
            path
        };
        let compiler = script(
            "fake-trustc",
            "printf 'rustc 1.99.0\\nbinary: rustc\\ncommit-hash: unknown\\nhost: aarch64-apple-darwin\\nrelease: 1.99.0\\n'",
        );
        let wrapper = script("fake-tippy-driver", "exec \"$@\"");
        let rustc = crate::util::Rustc::new(
            compiler.clone(),
            None,
            Some(wrapper.clone()),
            std::path::Path::new("/nonexistent/rustup/rustc"),
            None,
            &gctx,
        )
        .expect("the fake compiler answers -vV through the wrapper");

        let branded = super::target_info_probe_process(&rustc, true);
        assert_eq!(branded.get_program(), compiler.as_os_str());
        assert!(
            branded.get_args().all(|arg| arg != wrapper.as_os_str()),
            "the branded probe went through the workspace wrapper"
        );
        let ordinary = super::target_info_probe_process(&rustc, false);
        assert_eq!(ordinary.get_program(), wrapper.as_os_str());
        assert!(ordinary.get_args().any(|arg| arg == compiler.as_os_str()));
    }

    /// Trust (DECISION_QUEUE TARGO-PROBE-LANE-1): the verified lane's probe
    /// flags are what they were before the ruling: the project's flags and the
    /// lane's, minus every Trust option, with no off-switch and no second query.
    #[test]
    fn the_verified_lane_probe_flags_are_unchanged() {
        let (_temp, gctx) = context(ATERM_TABLE, &[], false);
        let lane = verified_lane();
        let (resolved, _) = resolve(&gctx, &lane).unwrap();
        let probe_lane = TargetInfoProbeLane::CompilerDefault;
        assert!(!probe_lane.keeps_off_switch(&resolved));
        assert_eq!(
            target_info_probe_flags(&resolved, probe_lane),
            strings(&[
                "--cfg",
                "clean_islands",
                "-Zthreads=4",
                "-Z",
                "codegen-backend=llvm",
                "-C",
                "overflow-checks=yes",
                "-C",
                "debug-assertions=yes",
            ])
        );
    }

    /// Trust (DECISION_QUEUE TARGO-PROBE-LANE-1): the explicitly unverified
    /// lane's resolved flags (the caller's, then Targo's off-switch) give a
    /// probe that answers as the lane's units compile, and a default query that
    /// a verifying-by-default compiler answers without refusing anything.
    /// Before, the probe got neither the off-switch nor its own `-Zcontract-checks`
    /// answer: it was `-Copt-level=3 -Zcontract-checks` at the verifying default,
    /// which refused it.
    #[test]
    fn the_unverified_lane_probe_answers_as_its_units_compile() {
        let (_temp, gctx) = context(
            ATERM_TABLE,
            &[(
                "RUSTFLAGS",
                "-Copt-level=3 -Zcontract-checks -Zinline-mir -Ztrust-verify-level=1",
            )],
            false,
        );
        let lane = TrustLane::new(false, true, Flags::Rust, None).unwrap();
        let (resolved, _) = resolve(&gctx, &lane).unwrap();
        assert_eq!(
            resolved,
            strings(&[
                "-Copt-level=3",
                "-Zcontract-checks",
                "-Zinline-mir",
                "-Ztrust-verify-level=1",
                "-Ztrust-verify=off",
            ])
        );
        let probe_lane = TargetInfoProbeLane::ExplicitlyUnverified;
        assert!(probe_lane.keeps_off_switch(&resolved));
        assert_eq!(
            target_info_probe_flags(&resolved, probe_lane),
            strings(&["-Copt-level=3", "-Zcontract-checks", "-Ztrust-verify=off"])
        );
        assert_eq!(
            trust_verify_default_query_flags(&resolved),
            strings(&["-Copt-level=3"])
        );
    }

    /// Trust (DECISION_QUEUE TARGO-PROBE-LANE-1): the default `trust_verify`
    /// query is `- --crate-name ___ --print=cfg <flags> [--target]`, run on the
    /// probe's program (never the workspace wrapper in a branded run, T14b),
    /// and through the rustc output cache. A fake compiler that verifies by
    /// default, refuses `-Zcontract-checks` while verifying, and forces the
    /// checks on, answers it with `trust_verify`.
    #[cfg(unix)]
    #[test]
    fn the_default_trust_verify_query_runs_at_the_compiler_default() {
        use std::os::unix::fs::PermissionsExt as _;

        let (temp, gctx) = context("", &[], false);
        let log = temp.path().join("argv.log");
        let script = |name: &str, body: &str| {
            let path = temp.path().join(name);
            std::fs::write(&path, format!("#!/bin/sh\n{body}\n")).unwrap();
            let mut permissions = std::fs::metadata(&path).unwrap().permissions();
            permissions.set_mode(0o755);
            std::fs::set_permissions(&path, permissions).unwrap();
            path
        };
        let compiler = script(
            "fake-trustc",
            &format!(
                r#"if [ "$1" = "-vV" ]; then
  printf 'rustc 1.99.0\nbinary: rustc\ncommit-hash: unknown\nhost: {HOST}\nrelease: 1.99.0\n'
  exit 0
fi
echo "$*" >> '{log}'
case " $* " in
  *" -Ztrust-verify=off "*) printf 'contract_checks\nunix\n'; exit 0 ;;
  *" -Zcontract-checks "*) echo 'error: -Zcontract-checks is retired' >&2; exit 1 ;;
esac
printf 'debug_assertions\noverflow_checks\ntrust_verify\nub_checks\nunix\n'"#,
                log = log.display(),
            ),
        );
        let wrapper = script("fake-tippy-driver", "exec \"$@\"");
        let rustc = crate::util::Rustc::new(
            compiler.clone(),
            None,
            Some(wrapper.clone()),
            std::path::Path::new("/nonexistent/rustup/rustc"),
            None,
            &gctx,
        )
        .expect("the fake compiler answers -vV");

        let resolved = strings(&["-Copt-level=3", "-Zcontract-checks", "-Ztrust-verify=off"]);
        let query =
            trust_verify_default_query_process(&gctx, &rustc, CompileKind::Host, &resolved, true)
                .unwrap();
        assert_eq!(query.get_program(), compiler.as_os_str());
        let (output, _) = rustc.cached_output(&query, 0).unwrap();
        assert!(reports_trust_verify(&output), "{output}");
        assert_eq!(
            std::fs::read_to_string(&log).unwrap(),
            "- --crate-name ___ --print=cfg -Copt-level=3\n"
        );
        // The lane's probe flags, by contrast, answer as its units compile.
        let probe = target_info_probe_flags(&resolved, TargetInfoProbeLane::ExplicitlyUnverified);
        let units = std::process::Command::new(&compiler)
            .args(&probe)
            .output()
            .unwrap();
        assert!(units.status.success());
        assert_eq!(
            String::from_utf8_lossy(&units.stdout),
            "contract_checks\nunix\n"
        );

        let target = CompileKind::Target(CompileTarget::Tuple("aarch64-unknown-linux-gnu".into()));
        let targeted =
            trust_verify_default_query_process(&gctx, &rustc, target, &resolved, false).unwrap();
        assert_eq!(targeted.get_program(), wrapper.as_os_str());
        assert_eq!(
            targeted
                .get_args()
                .map(|arg| arg.to_str().unwrap())
                .collect::<Vec<_>>(),
            [
                compiler.to_str().unwrap(),
                "-",
                "--crate-name",
                "___",
                "--print=cfg",
                "-Copt-level=3",
                "--target",
                "aarch64-unknown-linux-gnu",
            ]
        );
    }

    /// Trust (DECISION_QUEUE TARGO-PROBE-LANE-1): the probe's lane is derived
    /// from the lane `extra_args` resolves the Rust flags in. The explicitly
    /// unverified lane (`targo --unverified`, `targo tippy`) keeps its
    /// off-switch in the probe. The verified lane and ordinary Cargo answer at
    /// the compiler's default, and so does a `targo trust` selection probe that
    /// runs in the unverified lane with a lane handed to it (the trust-cg
    /// unit-graph preflight), which resolves the graph of the verified build it
    /// guards. Before the review fix the preflight's probe kept the off-switch.
    #[test]
    fn the_probe_lane_follows_the_lane_extra_args_resolves() {
        let unverified = TrustLane::new(false, true, Flags::Rust, None).unwrap();
        assert_eq!(
            TargetInfoProbeLane::of(&unverified),
            TargetInfoProbeLane::ExplicitlyUnverified
        );
        for probe_lane in [
            Vec::new(),
            strings(&[
                "-C",
                "panic=abort",
                "-C",
                "debuginfo=0",
                "-C",
                "codegen-units=1",
            ]),
            strings(&["-C", "overflow-checks=yes", "-C", "debug-assertions=yes"]),
        ] {
            let preflight = TrustLane::new(false, true, Flags::Rust, Some(probe_lane)).unwrap();
            assert_eq!(
                TargetInfoProbeLane::of(&preflight),
                TargetInfoProbeLane::CompilerDefault,
                "{preflight:?}"
            );
        }
        for lane in [
            verified_lane(),
            TrustLane::new(false, false, Flags::Rust, None).unwrap(),
            TrustLane::new(false, false, Flags::Rust, Some(Vec::new())).unwrap(),
        ] {
            assert_eq!(
                TargetInfoProbeLane::of(&lane),
                TargetInfoProbeLane::CompilerDefault,
                "{lane:?}"
            );
        }
    }

    /// The probes of `TargetInfo::new_in_lane` that `fake_verifying_trustc`
    /// logged, one argv per line.
    #[cfg(unix)]
    fn logged_probes(log: &std::path::Path) -> Vec<String> {
        std::fs::read_to_string(log)
            .unwrap_or_default()
            .lines()
            .map(str::to_string)
            .collect()
    }

    /// A fake `trustc` that verifies by default, as the installed pack does:
    /// unless its flags turn verification off it refuses `-Zcontract-checks`
    /// and reports `debug_assertions`, `overflow_checks`, `trust_verify` and
    /// `ub_checks`. It answers Cargo's target-info probe, logs each argv, and
    /// lists `contract_checks` and `--cfg clean_islands` as rustc does.
    #[cfg(unix)]
    fn fake_verifying_trustc(dir: &std::path::Path, log: &std::path::Path) -> std::path::PathBuf {
        fake_verifying_trustc_with_probe_output(dir, log, None)
    }

    #[cfg(unix)]
    fn fake_verifying_trustc_with_probe_output(
        dir: &std::path::Path,
        log: &std::path::Path,
        output: Option<(&str, &str)>,
    ) -> std::path::PathBuf {
        use std::os::unix::fs::PermissionsExt as _;

        let path = dir.join("fake-verifying-trustc");
        let probe_output = if let Some((stdout, stderr)) = output {
            std::fs::write(path.with_extension("stdout"), stdout).unwrap();
            std::fs::write(path.with_extension("stderr"), stderr).unwrap();
            "cat \"$0.stdout\"\n    cat \"$0.stderr\" >&2\n    exit 0"
        } else {
            "printf '___\\nlib___.rlib\\nlib___.dylib\\nlib___.dylib\\nlib___.a\\nlib___.dylib\\n'\n    printf '/fake/sysroot\\npacked\\nunpacked\\n___\\n'"
        };
        let body = format!(
            r#"#!/bin/sh
if [ "$1" = "-vV" ]; then
  printf 'rustc 1.99.0\nbinary: rustc\ncommit-hash: unknown\nhost: {HOST}\nrelease: 1.99.0\n'
  exit 0
fi
echo "$*" >> '{log}'
args=" $* "
case "$args" in
  *" -Ztrust-verify=off "*) verify=off ;;
  *) verify=on ;;
esac
if [ "$verify" = on ]; then
  case "$args" in
    *" -Zcontract-checks "*) echo 'error: -Zcontract-checks is retired' >&2; exit 1 ;;
  esac
fi
case "$args" in
  *" --print=file-names "*)
    {probe_output} ;;
esac
case "$args" in *" --cfg clean_islands "*) echo clean_islands ;; esac
case "$args" in *" -Zcontract-checks "*) echo contract_checks ;; esac
if [ "$verify" = on ]; then
  printf 'debug_assertions\noverflow_checks\ntrust_verify\nub_checks\n'
fi
echo unix
"#,
            log = log.display(),
        );
        std::fs::write(&path, body).unwrap();
        let mut permissions = std::fs::metadata(&path).unwrap().permissions();
        permissions.set_mode(0o755);
        std::fs::set_permissions(&path, permissions).unwrap();
        path
    }

    #[cfg(unix)]
    fn target_info_with_combined_probe(
        dir: &std::path::Path,
        gctx: &GlobalContext,
        stdout: &str,
        stderr: &str,
    ) -> crate::CargoResult<TargetInfo> {
        let compiler = fake_verifying_trustc_with_probe_output(
            dir,
            &dir.join("probes.log"),
            Some((stdout, stderr)),
        );
        let rustc = crate::util::Rustc::new(
            compiler,
            None,
            None,
            std::path::Path::new("/nonexistent/rustup/rustc"),
            None,
            gctx,
        )?;
        let lane = TrustLane::new(false, true, Flags::Rust, None)?;
        TargetInfo::new_in_lane(
            gctx,
            &[CompileKind::Host],
            &rustc,
            CompileKind::Host,
            &lane,
            true,
        )
    }

    #[cfg(unix)]
    fn combined_probe_output(sysroot: &std::path::Path) -> String {
        format!(
            "___\nlib___.rlib\nlib___.dylib\nlib___.dylib\nlib___.a\nlib___.dylib\n{}\npacked\nunpacked\n___\nunix\n",
            sysroot.display()
        )
    }

    #[cfg(unix)]
    #[test]
    fn target_info_combined_probe_preserves_sysroot_and_remaining_records() {
        let (temp, gctx) = context("", &[], false);
        let sysroot = temp.path().join("sysroot");
        std::fs::create_dir(&sysroot).unwrap();
        let info = target_info_with_combined_probe(
            temp.path(),
            &gctx,
            &combined_probe_output(&sysroot),
            "",
        )
        .unwrap();
        assert_eq!(info.sysroot, sysroot);
        assert_eq!(
            info.sysroot_target_libdir,
            sysroot.join("lib/rustlib").join(HOST).join("lib")
        );
        assert_eq!(
            info.support_split_debuginfo,
            strings(&["packed", "unpacked"])
        );
        assert!(info.cfg().iter().any(|cfg| cfg.to_string() == "unix"));
        assert_eq!(
            info.crate_types.borrow().get(&super::CrateType::Rlib),
            Some(&Some(("lib".into(), ".rlib".into())))
        );
    }

    #[cfg(unix)]
    #[test]
    fn target_info_combined_probe_preserves_filename_whitespace() {
        let (temp, gctx) = context("", &[], false);
        // rustc prints the basename verbatim. A target's DLL prefix/suffix can
        // include spaces; they are filename data, never presentation padding.
        let output = combined_probe_output(temp.path()).replace("lib___.dylib", " lib ___ .dylib ");
        let info = target_info_with_combined_probe(temp.path(), &gctx, &output, "").unwrap();
        assert_eq!(
            info.crate_types.borrow().get(&super::CrateType::Dylib),
            Some(&Some((" lib ".into(), " .dylib ".into())))
        );
        assert_eq!(info.sysroot, temp.path());
    }

    #[cfg(unix)]
    #[test]
    fn target_info_combined_probe_refuses_separate_filename_markers() {
        for filename in ["pre______.dylib", "lib___post___.dylib"] {
            let (temp, gctx) = context("", &[], false);
            let output = combined_probe_output(temp.path()).replace("lib___.dylib", filename);
            let error = target_info_with_combined_probe(temp.path(), &gctx, &output, "")
                .err()
                .expect("multiple marker positions cannot identify one filename template");
            assert!(
                error.to_string().contains("ambiguous"),
                "{filename}: {error:#}"
            );
        }
    }

    #[cfg(unix)]
    #[test]
    fn target_info_combined_probe_refuses_overlapping_filename_markers() {
        for filename in ["lib____.dylib", "lib_____.dylib"] {
            let (temp, gctx) = context("", &[], false);
            let output = combined_probe_output(temp.path()).replace("lib___.dylib", filename);
            let error = target_info_with_combined_probe(temp.path(), &gctx, &output, "")
                .err()
                .expect("overlapping marker positions are ambiguous too");
            assert!(
                error.to_string().contains("ambiguous"),
                "{filename}: {error:#}"
            );
        }
    }

    #[cfg(unix)]
    #[test]
    fn target_info_combined_probe_preserves_unicode_filename_data() {
        let (temp, gctx) = context("", &[], false);
        let output = combined_probe_output(temp.path()).replace("lib___.dylib", "λ-___.共享");
        let info = target_info_with_combined_probe(temp.path(), &gctx, &output, "").unwrap();
        assert_eq!(
            info.crate_types.borrow().get(&super::CrateType::Dylib),
            Some(&Some(("λ-".into(), ".共享".into())))
        );
        assert_eq!(info.sysroot, temp.path());
    }

    #[cfg(unix)]
    #[test]
    fn target_info_combined_probe_refuses_cr_instead_of_selecting_an_existing_sibling() {
        let (temp, gctx) = context("", &[], false);
        let ordinary = temp.path().join("sysroot");
        let selected = temp.path().join("sysroot\r");
        std::fs::create_dir(&ordinary).unwrap();
        std::fs::create_dir(&selected).unwrap();
        assert!(ordinary.is_dir() && selected.is_dir());
        let error = target_info_with_combined_probe(
            temp.path(),
            &gctx,
            &combined_probe_output(&selected),
            "",
        )
        .err()
        .expect("a CR-ending Unix path must not select its ordinary sibling");
        assert!(error.to_string().contains("carriage return"), "{error:#}");
    }

    #[cfg(unix)]
    #[test]
    fn target_info_combined_probe_refuses_cr_in_filename_and_cfg_records() {
        for region in ["filename", "cfg"] {
            let (temp, gctx) = context("", &[], false);
            let mut output = combined_probe_output(temp.path());
            output = if region == "filename" {
                output.replacen("___\n", "___\r\n", 1)
            } else {
                output.replace("unix\n", "unix\r\n")
            };
            let error = target_info_with_combined_probe(temp.path(), &gctx, &output, "")
                .err()
                .expect("CR must be refused before any record is normalized");
            assert!(
                error.to_string().contains("carriage return"),
                "{region}: {error:#}"
            );
        }
    }

    #[cfg(unix)]
    #[test]
    fn target_info_combined_probe_retains_missing_and_unsupported_record_handling() {
        let filenames = "___\nlib___.rlib\nlib___.dylib\nlib___.dylib\nlib___.a\nlib___.dylib\n";
        for (output, request) in [
            (filenames.to_owned(), "--print=sysroot"),
            (
                format!("{filenames}/fake/sysroot\npacked\nunix\n"),
                "--print=split-debuginfo",
            ),
        ] {
            let (temp, gctx) = context("", &[], false);
            let error = target_info_with_combined_probe(temp.path(), &gctx, &output, "")
                .err()
                .expect("missing protocol records must retain their refusal");
            assert!(error.to_string().contains(request), "{request}: {error:#}");
        }
        let (temp, gctx) = context("", &[], false);
        let output = combined_probe_output(temp.path()).replacen("lib___.dylib\n", "", 1);
        let info = target_info_with_combined_probe(
            temp.path(),
            &gctx,
            &output,
            "warning: unsupported crate type `dylib`\n",
        )
        .unwrap();
        assert_eq!(info.sysroot, temp.path());
        assert_eq!(
            info.crate_types.borrow().get(&super::CrateType::Dylib),
            Some(&None)
        );
    }

    /// `TargetInfo::new_in_lane` over `fake_verifying_trustc`: the cfg set, the
    /// resolved rustflags (which `[target.'cfg(..)']` table they came from) and
    /// the logged probes.
    #[cfg(unix)]
    fn target_info_in_lane(
        config: &str,
        lane: &TrustLane,
    ) -> (Vec<String>, Vec<String>, Vec<String>) {
        let (temp, gctx) = context(config, &[], false);
        let log = temp.path().join("probes.log");
        let compiler = fake_verifying_trustc(temp.path(), &log);
        let rustc = crate::util::Rustc::new(
            compiler,
            None,
            None,
            std::path::Path::new("/nonexistent/rustup/rustc"),
            None,
            &gctx,
        )
        .expect("the fake compiler answers -vV");
        let info = TargetInfo::new_in_lane(
            &gctx,
            &[CompileKind::Host],
            &rustc,
            CompileKind::Host,
            lane,
            true,
        )
        .unwrap();
        let cfg = info.cfg().iter().map(ToString::to_string).collect();
        (cfg, info.rustflags.to_vec(), logged_probes(&log))
    }

    /// The crate types and prints of the target-info probe after its flags.
    #[cfg(unix)]
    const PROBE_TAIL: &str = "--crate-type bin --crate-type rlib --crate-type dylib \
        --crate-type cdylib --crate-type staticlib --crate-type proc-macro --print=sysroot \
        --print=split-debuginfo --print=crate-name --print=cfg -Wwarnings";

    /// Trust (DECISION_QUEUE TARGO-PROBE-LANE-1): `TargetInfo` wired end to
    /// end in the explicitly unverified lane, over a compiler that verifies by
    /// default. The probe keeps the lane's off-switch, so `-Zcontract-checks`
    /// is answered (not refused) and no verification-forced cfg is reported;
    /// the default query supplies `trust_verify`, so the
    /// `[target.'cfg(trust_verify)']` table reaches the lane's units on the
    /// second turn (T14-TIPPY-1). Before the change the first probe was
    /// refused; without the query's `trust_verify` the table never applies.
    #[cfg(unix)]
    #[test]
    fn target_info_in_the_unverified_lane_answers_as_its_units_compile() {
        let config = r#"
[build]
rustflags = ["-Copt-level=3", "-Zcontract-checks"]

[target.'cfg(trust_verify)']
rustflags = ["--cfg", "clean_islands", "-Copt-level=3", "-Zcontract-checks"]
"#;
        let lane = TrustLane::new(false, true, Flags::Rust, None).unwrap();
        let (cfg, rustflags, probes) = target_info_in_lane(config, &lane);
        assert_eq!(
            cfg,
            strings(&["clean_islands", "contract_checks", "trust_verify", "unix"])
        );
        assert_eq!(
            rustflags,
            strings(&[
                "--cfg",
                "clean_islands",
                "-Copt-level=3",
                "-Zcontract-checks",
                "-Ztrust-verify=off",
            ])
        );
        assert_eq!(
            probes,
            [
                format!(
                    "- --crate-name ___ --print=file-names -Copt-level=3 -Zcontract-checks \
                     -Ztrust-verify=off {PROBE_TAIL}"
                ),
                "- --crate-name ___ --print=cfg -Copt-level=3".to_string(),
                format!(
                    "- --crate-name ___ --print=file-names --cfg clean_islands -Copt-level=3 \
                     -Zcontract-checks -Ztrust-verify=off {PROBE_TAIL}"
                ),
                "- --crate-name ___ --print=cfg --cfg clean_islands -Copt-level=3".to_string(),
            ]
        );
    }

    /// Trust (DECISION_QUEUE TARGO-PROBE-LANE-1, review fix): the trust-cg
    /// unit-graph preflight runs in the unverified lane with `targo trust`'s
    /// probe lane handed to it, and must select the tables and dependencies
    /// the verified build it guards selects. Its probe answers at the
    /// compiler's default (no off-switch, no second query), as the verified
    /// build's does, so a `cfg(overflow_checks)` table applies. Before the
    /// review fix the probe kept the off-switch and the table did not apply.
    #[cfg(unix)]
    #[test]
    fn target_info_of_a_selection_probe_answers_as_the_verified_build() {
        let config = r#"
[build]
rustflags = ["-Copt-level=3"]

[target.'cfg(overflow_checks)']
rustflags = ["--cfg", "ov", "-Copt-level=3"]
"#;
        let probe_lane = strings(&[
            "-C",
            "panic=abort",
            "-C",
            "debuginfo=0",
            "-C",
            "codegen-units=1",
        ]);
        let lane = TrustLane::new(false, true, Flags::Rust, Some(probe_lane)).unwrap();
        let (cfg, rustflags, probes) = target_info_in_lane(config, &lane);
        assert_eq!(
            cfg,
            strings(&[
                "debug_assertions",
                "overflow_checks",
                "trust_verify",
                "ub_checks",
                "unix"
            ])
        );
        assert_eq!(
            rustflags,
            strings(&[
                "--cfg",
                "ov",
                "-Copt-level=3",
                "-C",
                "panic=abort",
                "-C",
                "debuginfo=0",
                "-C",
                "codegen-units=1",
                "-Ztrust-verify=off",
            ])
        );
        let lane_tail = "-C panic=abort -C debuginfo=0 -C codegen-units=1";
        assert_eq!(
            probes,
            [
                format!(
                    "- --crate-name ___ --print=file-names -Copt-level=3 {lane_tail} {PROBE_TAIL}"
                ),
                format!(
                    "- --crate-name ___ --print=file-names --cfg ov -Copt-level=3 {lane_tail} \
                     {PROBE_TAIL}"
                ),
            ]
        );
    }

    /// Trust (DECISION_QUEUE TARGO-PROBE-LANE-1): `TargetInfo` wired end to
    /// end in the verified lane: its probe drops every Trust option and runs
    /// at the compiler's default, and no second query runs.
    #[cfg(unix)]
    #[test]
    fn target_info_in_the_verified_lane_probes_at_the_default_only() {
        let (cfg, rustflags, probes) = target_info_in_lane(ATERM_TABLE, &verified_lane());
        assert_eq!(
            cfg,
            strings(&[
                "clean_islands",
                "debug_assertions",
                "overflow_checks",
                "trust_verify",
                "ub_checks",
                "unix"
            ])
        );
        let mut expected = strings(&["--cfg", "clean_islands", "-Zthreads=4"]);
        expected.extend(verified_lane_flags());
        assert_eq!(rustflags, expected);
        let lane_tail = "-Z codegen-backend=llvm -C overflow-checks=yes -C debug-assertions=yes";
        assert_eq!(
            probes,
            [
                format!("- --crate-name ___ --print=file-names {lane_tail} {PROBE_TAIL}"),
                format!(
                    "- --crate-name ___ --print=file-names --cfg clean_islands -Zthreads=4 \
                     {lane_tail} {PROBE_TAIL}"
                ),
            ]
        );
    }
}
