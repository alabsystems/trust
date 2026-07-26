//! This modules contains types storing information of target platforms.
//!
//! Normally, call [`RustcTargetData::new`] to construct all the target
//! platform once, and then query info on your demand. For example,
//!
//! * [`RustcTargetData::dep_platform_activated`] to check if platform is activated.
//! * [`RustcTargetData::info`] to get a [`TargetInfo`] for an in-depth query.
//! * [`TargetInfo::rustc_outputs`] to get a list of supported file types.

use crate::core::compiler::CompileKind;
use crate::core::compiler::CompileMode;
use crate::core::compiler::CompileTarget;
use crate::core::compiler::CrateType;
use crate::core::compiler::apply_env_config;
use crate::core::{Dependency, Package, Target, TargetKind, Workspace};
use crate::util::context::{GlobalContext, StringList, TargetConfig};
use crate::util::interning::InternedString;
use crate::util::rustc_options::{
    canonical_codegen_backend_value, parse_rustflags_os, rustc_option_parts,
};
use crate::util::{CargoResult, Rustc};

use anyhow::Context as _;
use cargo_platform::{Cfg, CfgExpr};
use cargo_util::ProcessBuilder;
use serde::Deserialize;

use std::cell::RefCell;
use std::collections::HashSet;
use std::collections::hash_map::{Entry, HashMap};
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
    let output = process
        .exec_with_output()
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

// Trust: target-info probes are `--print` queries over stdin and compile no
// crate. Targo's authenticated Trust policy must remain in `TargetInfo::rustflags`
// for real units and fingerprinting, but passing it to the early-exit probe is
// both meaningless and rejected by trustc.  Rustc accepts `-`/`_` aliases, so
// classify through the same canonical option parser rather than matching one
// spelling.
fn strip_trust_verify_probe_flags(flags: &[String]) -> Vec<String> {
    fn is_trust_directive(value: &str) -> bool {
        let body = value
            .strip_prefix("-Z")
            .map(str::trim_start)
            .unwrap_or(value);
        let (name, _) = rustc_option_parts(body);
        name.starts_with("trust_")
    }

    let mut out = Vec::with_capacity(flags.len());
    let mut i = 0;
    while i < flags.len() {
        if flags[i] == "-Z"
            && flags
                .get(i + 1)
                .is_some_and(|value| is_trust_directive(value))
        {
            i += 2;
            continue;
        }
        if is_trust_directive(&flags[i]) {
            i += 1;
            continue;
        }
        out.push(flags[i].clone());
        i += 1;
    }
    out
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
        let mut rustflags =
            extra_args(gctx, requested_kinds, &rustc.host, None, kind, Flags::Rust)?;
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
            let mut process = rustc.workspace_process();
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
                .args(&strip_trust_verify_probe_flags(&rustflags))
                .env_remove("RUSTC_LOG");

            // Removes `FD_CLOEXEC` set by `jobserver::Client` to pass jobserver
            // as environment variables specify.
            if let Some(client) = gctx.jobserver_from_env() {
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

            let mut lines = output.lines();
            let mut map = HashMap::new();
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

            let cfg = lines
                .map(|line| Ok(Cfg::from_str(line)?))
                .filter(TargetInfo::not_user_specific_cfg)
                .collect::<CargoResult<Vec<_>>>()
                .with_context(|| {
                    format!(
                        "failed to parse the cfg from `rustc --print=cfg`, got:\n{}",
                        output
                    )
                })?;

            // recalculate `rustflags` from above now that we have `cfg`
            // information
            let new_flags = extra_args(
                gctx,
                requested_kinds,
                &rustc.host,
                Some(&cfg),
                kind,
                Flags::Rust,
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
                let mut target_spec_process = rustc.workspace_process();
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
                    .args(&strip_trust_verify_probe_flags(&rustflags))
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

                if let Ok(output) = target_spec_process.output() {
                    if let Ok(spec) = serde_json::from_slice::<TargetSpec>(&output.stdout) {
                        supports_std = spec.metadata.std;
                    }
                }
            }

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
            });
        }
    }

    fn not_user_specific_cfg(cfg: &CargoResult<Cfg>) -> bool {
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
        target_triple: &str,
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
            if target_triple.ends_with("-windows-msvc") && suffix == ".dll" {
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
                && (target_triple.ends_with("windows-gnu")
                    || target_triple.ends_with("windows-gnullvm")
                    || target_triple.ends_with("cygwin"))
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

        if target_triple.starts_with("wasm32-") && crate_type == CrateType::Bin && suffix == ".js" {
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
        let is_apple = target_triple.contains("-apple-");
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
            } else if target_triple.ends_with("-msvc") || target_triple.ends_with("-uefi") {
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

        let output = process.exec_with_output().with_context(|| {
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
        target_triple: &str,
        gctx: &GlobalContext,
    ) -> CargoResult<(Vec<FileType>, Vec<CrateType>)> {
        match mode {
            CompileMode::Build => self.calc_rustc_outputs(target_kind, target_triple, gctx),
            CompileMode::Test => {
                match self.file_types(&CrateType::Bin, FileFlavor::Normal, target_triple)? {
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
        target_triple: &str,
        gctx: &GlobalContext,
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
            let file_types = self.file_types(crate_type, flavor, target_triple)?;
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
            if gctx.cli_unstable().no_embed_metadata
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
    let mut parts = line.trim().split("___");
    let prefix = parts.next().unwrap();
    let Some(suffix) = parts.next() else {
        return error_missing_print_output("file-names", cmd, output, error);
    };

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
enum Flags {
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
        rustflags_from_host(gctx, flags, host_triple)?.unwrap_or_else(Vec::new)
    } else if let Some(rustflags) = rustflags_from_env(gctx, flags) {
        rustflags
    } else if let Some(rustflags) =
        rustflags_from_target(gctx, host_triple, target_cfg, kind, flags)?
    {
        rustflags
    } else if let Some(rustflags) = rustflags_from_build(gctx, flags)? {
        rustflags
    } else {
        Vec::new()
    };

    // Trust: `TargetInfo::new` uses these resolved flags for rustc `--print`
    // probes before compilation units (and their final-argv policy) exist,
    // which makes this the earliest flag boundary that exists at all. Reject the
    // retired Trust exec projection at this first resolved compiler-flags
    // boundary so ambient, target/build config, isolated `[host]`, and rustdoc
    // spellings cannot reach a probe or documentation subprocess.
    if crate::is_targo_invocation() && crate::trust_verified_targo() {
        reject_retired_contract_checks(&args)?;
    }

    // Trust: Cargo intentionally isolates explicit-target host artifacts (build
    // scripts and proc macros) from RUSTFLAGS. Verified Targo is the one
    // exception: every compiler unit participating in a proof must receive the
    // same verifier policy and session. Import only Targo's closed verifier
    // protocol, only after the branded frontend accepted the internal marker,
    // and do it here so Unit construction and Cargo fingerprinting see it.
    // Ordinary Cargo never reads (or attempts to Unicode-decode) the otherwise
    // ignored host RUSTFLAGS in this branch.
    if host_isolated
        && matches!(flags, Flags::Rust)
        && crate::is_targo_invocation()
        && crate::trust_verified_targo()
    {
        let policy = verified_targo_host_policy_from_env(
            true,
            gctx.get_env_os("CARGO_ENCODED_RUSTFLAGS"),
            gctx.get_env_os("RUSTFLAGS"),
        )?;
        let target_codegen_backend = verified_targo_target_codegen_backend_from_env(
            true,
            gctx.get_env_os("CARGO_ENCODED_RUSTFLAGS"),
            gctx.get_env_os("RUSTFLAGS"),
        )?;
        reject_host_config_trust_policy(&args, &policy)?;
        canonicalize_verified_targo_host_codegen_backend(
            &mut args,
            target_codegen_backend.as_deref(),
        )?;
        args.extend(policy);
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
    append_trust_no_verify_fast_flag(&mut args, crate::trust_no_verify_fast());

    Ok(args)
}

// Trust: from here to `rustflags_from_env` is Trust-authored. It is the
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
        args.push("-Ztrust-verify=off".to_string());
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
/// This is also the outer bound of targo-trust's TRUSTFLAGS override channel:
/// TRUSTFLAGS accepts exactly these options minus the reserved
/// authentication/transport entries (`trust_verify_session`,
/// `trust_proof_artifact_root`, `trust_verify_output`, plus the
/// Targo-reserved unit metadata below). Keep the two lists in sync when
/// extending the protocol (targo-trust/src/pipeline/trustflags.rs).
const VERIFIED_TARGO_HOST_POLICY_OPTIONS: &[&str] = &[
    "trust_cg_output_gate",
    "trust_proof_artifact_root",
    "trust_verify_ay_path",
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
    let mut seen = HashSet::new();
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

fn verified_targo_host_policy_from_env(
    enabled: bool,
    encoded: Option<&OsStr>,
    plain: Option<&OsStr>,
) -> CargoResult<Vec<String>> {
    // Keep this guard before decoding: ordinary Cargo historically ignores
    // these bytes for explicit-target host artifacts, including non-UTF-8
    // values on Unix.
    if !enabled {
        return Ok(Vec::new());
    }
    extract_verified_targo_host_policy(
        &parse_rustflags_os(encoded, plain).map_err(anyhow::Error::msg)?,
    )
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

fn verified_targo_target_codegen_backend_from_env(
    enabled: bool,
    encoded: Option<&OsStr>,
    plain: Option<&OsStr>,
) -> CargoResult<Option<String>> {
    if !enabled {
        return Ok(None);
    }
    verified_targo_target_codegen_backend(
        &parse_rustflags_os(encoded, plain).map_err(anyhow::Error::msg)?,
    )
}

/// An explicit Cargo target keeps build scripts and proc macros on the host
/// side of the rustflags boundary. When the target side selects trust-cg,
/// force those host-only units back onto LLVM: they require executable/dynamic
/// artifacts that trust-cg deliberately does not advertise. A competing
/// [host] backend is rejected instead of being silently reinterpreted.
fn canonicalize_verified_targo_host_codegen_backend(
    host_flags: &mut Vec<String>,
    target_codegen_backend: Option<&str>,
) -> CargoResult<()> {
    if target_codegen_backend != Some("trust-cg") {
        return Ok(());
    }

    let mut sanitized = Vec::with_capacity(host_flags.len() + 2);
    let mut index = 0;
    while index < host_flags.len() {
        let (option, split) = if host_flags[index] == "-Z" {
            (host_flags.get(index + 1).map(String::as_str), true)
        } else {
            (
                host_flags[index]
                    .strip_prefix("-Z")
                    .filter(|option| !option.is_empty()),
                false,
            )
        };
        if let Some(option) = option {
            let (name, value) = rustc_option_parts(option);
            if name != "codegen_backend" {
                sanitized.push(host_flags[index].clone());
                index += 1;
                continue;
            }
            let value = value.filter(|value| !value.is_empty());
            if value != Some("llvm") {
                anyhow::bail!(
                    "[host] rustflags select `{}` while verified trust-cg requires LLVM for build scripts and proc macros",
                    value.unwrap_or("<missing backend>")
                );
            }
            index += if split { 2 } else { 1 };
            continue;
        }
        sanitized.push(host_flags[index].clone());
        index += 1;
    }
    sanitized.extend(["-Z".to_string(), "codegen-backend=llvm".to_string()]);
    *host_flags = sanitized;
    Ok(())
}

fn reject_host_config_trust_policy(
    host_flags: &[String],
    imported_policy: &[String],
) -> CargoResult<()> {
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
            let (name, _) = rustc_option_parts(option);
            if option_class == 'Z' && name.starts_with("trust_") {
                anyhow::bail!(
                    "[host] rustflags cannot set -Z{name} during a verified Targo invocation"
                );
            }
            if option_class == 'C' && imported_safety_options.contains(name.as_ref()) {
                anyhow::bail!(
                    "[host] rustflags cannot set -C{name} while verified Targo imports that safety policy"
                );
            }
        }
        index += if split { 2 } else { 1 };
    }
    Ok(())
}

/// Gets compiler flags from environment variables.
/// See [`extra_args`] for more.
fn rustflags_from_env(gctx: &GlobalContext, flags: Flags) -> Option<Vec<String>> {
    // First try CARGO_ENCODED_RUSTFLAGS from the environment.
    // Prefer this over RUSTFLAGS since it's less prone to encoding errors.
    if let Ok(a) = gctx.get_env(format!("CARGO_ENCODED_{}", flags.as_env())) {
        if a.is_empty() {
            return Some(Vec::new());
        }
        return Some(a.split('\x1f').map(str::to_string).collect());
    }

    // Then try RUSTFLAGS from the environment
    if let Ok(a) = gctx.get_env(flags.as_env()) {
        let args = a
            .split(' ')
            .map(str::trim)
            .filter(|s| !s.is_empty())
            .map(str::to_string);
        return Some(args.collect());
    }

    // No rustflags to be collected from the environment
    None
}

/// Gets compiler flags from `[target]` section in the config.
/// See [`extra_args`] for more.
fn rustflags_from_target(
    gctx: &GlobalContext,
    host_triple: &str,
    target_cfg: Option<&[Cfg]>,
    kind: CompileKind,
    flag: Flags,
) -> CargoResult<Option<Vec<String>>> {
    let mut rustflags = Vec::new();

    // Then the target.*.rustflags value...
    let target = match &kind {
        CompileKind::Host => host_triple,
        CompileKind::Target(target) => target.short_name(),
    };
    let key = format!("target.{}.{}", target, flag.as_key());
    if let Some(args) = gctx.get::<Option<StringList>>(&key)? {
        rustflags.extend(args.as_slice().iter().cloned());
    }
    // ...including target.'cfg(...)'.rustflags
    if let Some(target_cfg) = target_cfg {
        gctx.target_cfgs()?
            .iter()
            .filter_map(|(key, cfg)| match flag {
                Flags::Rust => cfg
                    .rustflags
                    .as_ref()
                    .map(|rustflags| (key, &rustflags.val)),
                Flags::Rustdoc => cfg
                    .rustdocflags
                    .as_ref()
                    .map(|rustdocflags| (key, &rustdocflags.val)),
            })
            .filter(|(key, _rustflags)| CfgExpr::matches_key(key, target_cfg))
            .for_each(|(_key, cfg_rustflags)| {
                rustflags.extend(cfg_rustflags.as_slice().iter().cloned());
            });
    }

    if rustflags.is_empty() {
        Ok(None)
    } else {
        Ok(Some(rustflags))
    }
}

/// Gets compiler flags from `[host]` section in the config.
/// See [`extra_args`] for more.
fn rustflags_from_host(
    gctx: &GlobalContext,
    flag: Flags,
    host_triple: &str,
) -> CargoResult<Option<Vec<String>>> {
    let target_cfg = gctx.host_cfg_triple(host_triple)?;
    let list = match flag {
        Flags::Rust => &target_cfg.rustflags,
        Flags::Rustdoc => {
            // host.rustdocflags is not a thing, since it does not make sense
            return Ok(None);
        }
    };
    Ok(list.as_ref().map(|l| l.val.as_slice().to_vec()))
}

/// Gets compiler flags from `[build]` section in the config.
/// See [`extra_args`] for more.
fn rustflags_from_build(gctx: &GlobalContext, flag: Flags) -> CargoResult<Option<Vec<String>>> {
    // Then the `build.rustflags` value.
    let build = gctx.build_config()?;
    let list = match flag {
        Flags::Rust => &build.rustflags,
        Flags::Rustdoc => &build.rustdocflags,
    };
    Ok(list.as_ref().map(|l| l.as_slice().to_vec()))
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

impl<'gctx> RustcTargetData<'gctx> {
    #[tracing::instrument(skip_all)]
    pub fn new(
        ws: &Workspace<'gctx>,
        requested_kinds: &[CompileKind],
    ) -> CargoResult<RustcTargetData<'gctx>> {
        let gctx = ws.gctx();
        let rustc = gctx.load_global_rustc(Some(ws))?;
        let mut target_config = HashMap::new();
        let mut target_info = HashMap::new();
        let target_applies_to_host = gctx.target_applies_to_host()?;
        let host_target = CompileTarget::new(&rustc.host, gctx.cli_unstable().json_target_spec)?;
        let host_info = TargetInfo::new(gctx, requested_kinds, &rustc, CompileKind::Host)?;

        // This config is used for link overrides and choosing a linker.
        let host_config = if target_applies_to_host {
            gctx.target_cfg_triple(&rustc.host)?
        } else {
            gctx.host_cfg_triple(&rustc.host)?
        };

        // This is a hack. The unit_dependency graph builder "pretends" that
        // `CompileKind::Host` is `CompileKind::Target(host)` if the
        // `--target` flag is not specified. Since the unit_dependency code
        // needs access to the target config data, create a copy so that it
        // can be found. See `rebuild_unit_graph_shared` for why this is done.
        if requested_kinds.iter().any(CompileKind::is_host) {
            target_config.insert(host_target, gctx.target_cfg_triple(&rustc.host)?);

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
                self.target_config
                    .insert(target, self.gctx.target_cfg_triple(target.short_name())?);
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
        append_trust_no_verify_fast_flag, canonicalize_verified_targo_host_codegen_backend,
        extract_verified_targo_host_policy, reject_host_config_trust_policy,
        reject_retired_contract_checks, strip_trust_verify_probe_flags,
        verified_targo_named_target_error, verified_targo_target_codegen_backend,
        verified_targo_host_policy_from_env,
    };
    use crate::core::compiler::{CompileKind, CompileTarget};

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
            strings(&["-Ztrust-verify=off", "-Z", "trust_verify=on", "-Ztrust-verify=off"])
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
            strip_trust_verify_probe_flags(&flags),
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
            "trust_cg_output_gate" => format!("-Z{key}=strict"),
            "trust_verify_ay_path" => format!("-Z{key}=/toolchain/bin/ay"),
            "trust_verify_session" => format!("-Z{key}=proof-full-policy"),
            "trust_proof_artifact_root" => format!("-Z{key}=/tmp/trust-proof-full-policy"),
            "trust_verify_output" => format!("-Z{key}=json"),
            "trust_verify_level" => format!("-Z{key}=2"),
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

        let mut host = strings(&["-Cdebuginfo=2", "-Zcodegen-backend=llvm"]);
        canonicalize_verified_targo_host_codegen_backend(&mut host, Some("trust-cg"))
            .expect("matching host LLVM policy canonicalizes");
        assert_eq!(
            host,
            strings(&["-Cdebuginfo=2", "-Z", "codegen-backend=llvm"])
        );
        assert!(!host.iter().any(|arg| arg.contains("trust-cg")));

        let mut equivalent_host = strings(&["-Cdebuginfo=2", "-Zcodegen_backend=llvm"]);
        canonicalize_verified_targo_host_codegen_backend(&mut equivalent_host, Some("trust-cg"))
            .expect("rustc-equivalent host LLVM policy canonicalizes");
        assert_eq!(
            equivalent_host,
            strings(&["-Cdebuginfo=2", "-Z", "codegen-backend=llvm"])
        );
    }

    #[test]
    fn trust_cg_target_rejects_competing_host_codegen_backend() {
        for host in [
            strings(&["-Zcodegen-backend=cranelift"]),
            strings(&["-Z", "codegen-backend=trust-cg"]),
            strings(&["-Zcodegen_backend=trust-cg"]),
            strings(&["-Zcodegen-backend"]),
        ] {
            let mut host = host;
            let error =
                canonicalize_verified_targo_host_codegen_backend(&mut host, Some("trust-cg"))
                    .expect_err("host-only artifacts must not inherit a non-LLVM backend");
            assert!(error.to_string().contains("requires LLVM"), "{error:#}");
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
            let error = reject_host_config_trust_policy(&strings(&[host_flag]), &policy)
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
            let error = reject_host_config_trust_policy(&strings(&[host_flag]), &policy)
                .expect_err("host config must not compete with imported proof safety policy");
            assert!(error.to_string().contains("cannot set -C"), "{error:#}");
        }
        reject_host_config_trust_policy(&strings(&["-Ctarget-cpu=native"]), &policy)
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
        let first = verified_targo_host_policy_from_env(
            true,
            Some(OsStr::new(
                "-Z\x1ftrust-verify-session=proof-1\x1f-Z\x1ftrust-proof-artifact-root=/tmp/proof-1",
            )),
            None,
        )
        .unwrap();
        let second = verified_targo_host_policy_from_env(
            true,
            Some(OsStr::new(
                "-Z\x1ftrust-verify-session=proof-2\x1f-Z\x1ftrust-proof-artifact-root=/tmp/proof-2",
            )),
            None,
        )
        .unwrap();
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
    fn encoded_host_policy_takes_precedence_over_plain_rustflags() {
        let policy = verified_targo_host_policy_from_env(
            true,
            Some(OsStr::new(
                "-Z\x1ftrust-verify-level=1\x1f-Z\x1ftrust-verify-session=encoded\x1f-Z\x1ftrust-proof-artifact-root=/tmp/encoded",
            )),
            Some(OsStr::new(
                "-Z trust-verify-level=2 -Z trust-verify-session=plain -Z trust-proof-artifact-root=/tmp/plain",
            )),
        )
        .unwrap();
        assert!(policy.iter().any(|arg| arg == "trust-verify-level=1"));
        assert!(
            policy
                .iter()
                .any(|arg| arg == "trust-verify-session=encoded")
        );
        assert!(!policy.iter().any(|arg| arg.contains("plain")));
    }

    #[test]
    fn ordinary_cargo_keeps_cross_target_host_rustflags_isolated() {
        let policy = verified_targo_host_policy_from_env(
            false,
            Some(OsStr::new(
                "-Z\x1ftrust-verify-session=must-not-cross-host-boundary",
            )),
            None,
        )
        .unwrap();
        assert!(policy.is_empty());
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
    fn ignored_non_utf8_host_rustflags_remain_compatible_with_ordinary_cargo() {
        use std::os::unix::ffi::OsStringExt;

        let invalid = std::ffi::OsString::from_vec(vec![0xff, 0xfe]);
        assert!(
            verified_targo_host_policy_from_env(false, Some(&invalid), None)
                .unwrap()
                .is_empty()
        );
        let error = verified_targo_host_policy_from_env(true, Some(&invalid), None).unwrap_err();
        assert!(error.to_string().contains("not valid Unicode"), "{error:#}");
    }
}
