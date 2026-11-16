use std::any::Any;
use std::ffi::{OsStr, OsString};
use std::io::Write;
use std::path::{Path, PathBuf};
use std::sync::{Arc, LazyLock, OnceLock};
use std::{env, fs, iter};

use rustc_ast as ast;
use rustc_attr_ir::{Attribute, AttributeKind, find_attr};
use rustc_attr_parsing::{AttributeParser, ShouldEmit};
use rustc_codegen_ssa::traits::CodegenBackend;
use rustc_codegen_ssa::{CompiledModules, CrateInfo};
use rustc_crate_store::Untracked;
use rustc_data_structures::indexmap::IndexMap;
use rustc_data_structures::steal::Steal;
use rustc_data_structures::sync::{
    AppendOnlyIndexVec, DynSend, DynSync, FreezeLock, WorkerLocal, par_fns,
};
use rustc_data_structures::thousands;
use rustc_errors::timings::TimingSection;
use rustc_errors::{Diag, DiagCtxtHandle, Diagnostic, Level};
use rustc_expand::base::{ExtCtxt, LintStoreExpand};
use rustc_feature::Features;
use rustc_fs_util::try_canonicalize;
use rustc_hir::def_id::{LOCAL_CRATE, StableCrateId, StableCrateIdMap};
use rustc_hir::definitions::Definitions;
use rustc_incremental::setup_dep_graph;
use rustc_lint::{BufferedEarlyLint, EarlyCheckNode, LintStore, unerased_lint_store};
use rustc_metadata::EncodedMetadata;
use rustc_metadata::creader::CStore;
use rustc_middle::arena::Arena;
use rustc_middle::middle::resolve::{ResolverAstLowering, ResolverGlobalCtxt};
use rustc_middle::ty::{self, RegisteredTools, TyCtxt};
use rustc_middle::util::Providers;
use rustc_parse::lexer::StripTokens;
use rustc_parse::{new_parser_from_file, new_parser_from_source_str, unwrap_or_emit_fatal};
use rustc_passes::{abi_test, input_stats, layout_test};
use rustc_resolve::{Resolver, ResolverOutputs};
use rustc_session::config::{Input, OutFileName, OutputFilenames, OutputType};
use rustc_session::diagnostics::feature_err;
use rustc_session::output::{filename_for_input, invalid_output_for_target};
use rustc_session::search_paths::PathKind;
use rustc_session::{IncrCompSession, Session};
use rustc_span::{
    DUMMY_SP, ErrorGuaranteed, ExpnKind, SourceFileHash, SourceFileHashAlgorithm, Span, Symbol, sym,
};
use rustc_structures::CrateType;
use rustc_trait_selection::{solve, traits};
use tracing::{info, instrument};

use crate::interface::Compiler;
use crate::{diagnostics, limits, util};

// Trust: one owned representation and canonical formatter for dependency data.
mod dep_info;
pub use dep_info::PreparedDepInfo;
use dep_info::{escape_dep_env, escape_dep_filename};

pub fn parse<'a>(sess: &'a Session) -> ast::Crate {
    // Begin before input I/O: a parse error must leave an explicitly incomplete
    // census, never a stale complete roster from an earlier invocation.
    crate::trust_body_census::prepare(sess);
    rustc_mir_transform::trust_lean_census::prepare(
        sess,
        crate::util::rustc_version_str().unwrap_or("unknown"),
    );
    rustc_monomorphize::trust_instance_census::prepare(
        sess,
        crate::util::rustc_version_str().unwrap_or("unknown"),
    );
    let artifact_publication_requested =
        sess.trust_ir_lower_enabled() && sess.opts.unstable_opts.trust_dump.ir.is_some();
    if artifact_publication_requested {
        // The ordinary driver installed the exact pre-input writer lease in
        // this Session. This call is idempotent for that path and remains a
        // custom-driver fallback. Normal crate-name validation later requires
        // source and injected attributes to agree.
        let Some(crate_name) = sess.opts.crate_name.as_deref() else {
            sess.dcx().fatal(
                "-Ztrust-dump=ir:<dir> with -Ztrust-ir-lower requires an explicit --crate-name",
            );
        };
        rustc_session::output::validate_crate_name(sess, Symbol::intern(crate_name), None);
        rustc_mir_build::trust_ir_prepare_artifact_publication(sess, crate_name);
    }
    let mut krate = sess
        .time("parse_crate", || {
            let mut parser = unwrap_or_emit_fatal(match &sess.io.input {
                Input::File(file) => new_parser_from_file(
                    &sess.psess,
                    file,
                    StripTokens::ShebangAndFrontmatter,
                    None,
                ),
                instr @ (Input::Str { input, .. } | Input::DocTestStr { input, .. }) => {
                    new_parser_from_source_str(
                        &sess.psess,
                        instr.file_name(sess),
                        input.clone(),
                        StripTokens::ShebangAndFrontmatter,
                    )
                }
            });
            parser.parse_crate_mod()
        })
        .unwrap_or_else(|parse_error| {
            let guar: ErrorGuaranteed = parse_error.emit_err();
            guar.raise_fatal();
        });

    rustc_builtin_macros::cmdline_attrs::inject(
        &mut krate,
        &sess.psess,
        &sess.opts.unstable_opts.crate_attr,
    );

    krate
}

fn pre_expansion_lint<'a>(
    sess: &Session,
    features: &Features,
    lint_store: &LintStore,
    registered_lint_tools: &RegisteredTools,
    check_node: EarlyCheckNode<'a>,
    node_name: Symbol,
) {
    sess.prof.generic_activity_with_arg("pre_AST_expansion_lint_checks", node_name.as_str()).run(
        || {
            rustc_lint::check_ast_node(
                sess,
                features,
                true,
                lint_store,
                registered_lint_tools,
                None,
                check_node,
            );
        },
    );
}

// Cannot implement directly for `LintStore` due to trait coherence.
struct LintStoreExpandImpl<'a>(&'a LintStore);

impl LintStoreExpand for LintStoreExpandImpl<'_> {
    fn pre_expansion_lint(
        &self,
        sess: &Session,
        features: &Features,
        registered_lint_tools: &RegisteredTools,
        node_id: ast::NodeId,
        attrs: &[ast::Attribute],
        items: &[Box<ast::Item>],
        name: Symbol,
    ) {
        let check_node = EarlyCheckNode::LoadedMod(node_id, attrs, items);
        pre_expansion_lint(sess, features, self.0, registered_lint_tools, check_node, name);
    }
}

/// Runs the "early phases" of the compiler: initial `cfg` processing,
/// syntax expansion, secondary `cfg` expansion, synthesis of a test
/// harness if one is to be provided, injection of a dependency on the
/// standard library and prelude, and name resolution.
#[instrument(level = "trace", skip(krate, resolver))]
fn configure_and_expand(
    mut krate: ast::Crate,
    pre_configured_attrs: &[ast::Attribute],
    resolver: &mut Resolver<'_, '_>,
) -> ast::Crate {
    let tcx = resolver.tcx();
    let sess = tcx.sess;
    let features = tcx.features();
    let lint_store = unerased_lint_store(sess);
    let crate_name = tcx.crate_name(LOCAL_CRATE);
    pre_expansion_lint(
        sess,
        features,
        lint_store,
        tcx.registered_lint_tools(()),
        EarlyCheckNode::CrateRoot(&krate, pre_configured_attrs),
        crate_name,
    );
    rustc_builtin_macros::register_builtin_macros(resolver);

    let num_standard_library_imports = sess.time("crate_injection", || {
        rustc_builtin_macros::standard_library_imports::inject(
            &mut krate,
            pre_configured_attrs,
            resolver,
            sess,
            features,
        )
    });

    // Expand all macros
    krate = sess.time("macro_expand_crate", || {
        // Windows dlls do not have rpaths, so they don't know how to find their
        // dependencies. It's up to us to tell the system where to find all the
        // dependent dlls. Note that this uses cfg!(windows) as opposed to
        // targ_cfg because syntax extensions are always loaded for the host
        // compiler, not for the target.
        //
        // This is somewhat of an inherently racy operation, however, as
        // multiple threads calling this function could possibly continue
        // extending PATH far beyond what it should. To solve this for now we
        // just don't add any new elements to PATH which are already there
        // within PATH. This is basically a targeted fix at #17360 for rustdoc
        // which runs rustc in parallel but has been seen (#33844) to cause
        // problems with PATH becoming too long.
        let mut old_path = OsString::new();
        if cfg!(windows) {
            old_path = env::var_os("PATH").unwrap_or(old_path);
            let mut new_path = Vec::from_iter(
                sess.host_filesearch().search_paths(PathKind::Native).map(|p| p.dir.to_path_buf()),
            );
            for path in env::split_paths(&old_path) {
                if !new_path.contains(&path) {
                    new_path.push(path);
                }
            }
            // Blessed `env_mutation` site: pre-existing rustdoc PATH
            // workaround (see above); scoped, Windows-only, and restored
            // below.
            #[cfg_attr(not(bootstrap), allow(unknown_lints, env_mutation))]
            unsafe {
                env::set_var(
                    "PATH",
                    env::join_paths(
                        new_path.iter().filter(|p| env::join_paths(iter::once(p)).is_ok()),
                    )
                    .unwrap(),
                );
            }
        }

        // Create the config for macro expansion
        let recursion_limit = tcx.recursion_limit();
        let cfg = rustc_expand::expand::ExpansionConfig {
            crate_name,
            features,
            recursion_limit,
            trace_mac: sess.opts.unstable_opts.trace_macros,
            should_test: sess.is_test_crate(),
            span_debug: sess.opts.unstable_opts.span_debug,
            proc_macro_backtrace: sess.opts.unstable_opts.proc_macro_backtrace,
        };

        let lint_store = LintStoreExpandImpl(lint_store);
        let mut ecx = ExtCtxt::new(sess, cfg, resolver, Some(&lint_store));
        ecx.num_standard_library_imports = num_standard_library_imports;
        // Expand macros now!
        let krate = sess.time("expand_crate", || ecx.monotonic_expander().expand_crate(krate));

        if ecx.nb_macro_errors > 0 {
            sess.dcx().abort_if_errors();
        }

        // The rest is error reporting and stats

        sess.psess.buffered_lints.with_lock(|buffered_lints: &mut Vec<BufferedEarlyLint>| {
            buffered_lints.append(&mut ecx.buffered_early_lint);
        });

        sess.time("check_unused_macros", || {
            ecx.check_unused_macros();
        });

        // If we hit a recursion limit, exit early to avoid later passes getting overwhelmed
        // with a large AST
        if ecx.reduced_recursion_limit.is_some() {
            sess.dcx().abort_if_errors();
            unreachable!();
        }

        if cfg!(windows) {
            // Blessed `env_mutation` site: restores the PATH mutated above.
            #[cfg_attr(not(bootstrap), allow(unknown_lints, env_mutation))]
            unsafe {
                env::set_var("PATH", &old_path);
            }
        }

        if ecx.sess.opts.unstable_opts.macro_stats {
            print_macro_stats(&ecx);
        }

        krate
    });

    sess.time("maybe_building_test_harness", || {
        rustc_builtin_macros::test_harness::inject(&mut krate, sess, features, resolver)
    });

    let has_proc_macro_decls = sess.time("AST_validation", || {
        rustc_ast_passes::ast_validation::check_crate(
            sess,
            features,
            &krate,
            tcx.is_sdylib_interface_build(),
            resolver.lint_buffer(),
        )
    });

    if features.rustc_attrs() {
        rustc_ast_passes::show_spans::check_crate(sess, &krate);
    }

    let crate_types = tcx.crate_types();
    let is_executable_crate = crate_types.contains(&CrateType::Executable);
    let is_proc_macro_crate = crate_types.contains(&CrateType::ProcMacro);

    if crate_types.len() > 1 {
        if is_executable_crate {
            sess.dcx().emit_err(diagnostics::MixedBinCrate);
        }
        if is_proc_macro_crate {
            sess.dcx().emit_err(diagnostics::MixedProcMacroCrate);
        }
    }

    if is_proc_macro_crate && sess.target.is_like_wasm && !sess.opts.unstable_opts.wasm_proc_macros
    {
        sess.dcx().emit_err(diagnostics::UnstableWasmProcMacro);
    }

    if crate_types.contains(&CrateType::Sdylib) && !tcx.features().export_stable() {
        feature_err(sess, sym::export_stable, DUMMY_SP, "`sdylib` crate type is unstable").emit();
    }

    if is_proc_macro_crate && !sess.sanitizers().is_empty() {
        sess.dcx().emit_err(diagnostics::CannotSanitizeProcMacro);
    }

    if is_proc_macro_crate && !sess.panic_strategy().unwinds() {
        sess.dcx().emit_warn(diagnostics::ProcMacroCratePanicAbort);
    }

    sess.time("maybe_create_a_macro_crate", || {
        let is_test_crate = sess.is_test_crate();
        rustc_builtin_macros::proc_macro_harness::inject(
            &mut krate,
            sess,
            features,
            resolver,
            is_proc_macro_crate,
            has_proc_macro_decls,
            is_test_crate,
            sess.dcx(),
        )
    });

    // Done with macro expansion!

    resolver.resolve_crate(&krate);

    CStore::from_tcx(tcx).report_session_incompatibilities(tcx, &krate);
    krate
}

fn print_macro_stats(ecx: &ExtCtxt<'_>) {
    use std::fmt::Write;

    let crate_name = ecx.ecfg.crate_name.as_str();
    let crate_name = if crate_name == "build_script_build" {
        // This is a build script. Get the package name from the environment.
        let pkg_name =
            std::env::var("CARGO_PKG_NAME").unwrap_or_else(|_| "<unknown crate>".to_string());
        format!("{pkg_name} build script")
    } else {
        crate_name.to_string()
    };

    // No instability because we immediately sort the produced vector.
    #[allow(rustc::potential_query_instability)]
    let mut macro_stats: Vec<_> = ecx
        .macro_stats
        .iter()
        .map(|((name, kind), stat)| {
            // This gives the desired sort order: sort by bytes, then lines, etc.
            (stat.bytes, stat.lines, stat.uses, name, *kind)
        })
        .collect();
    macro_stats.sort_unstable();
    macro_stats.reverse(); // bigger items first

    let prefix = "macro-stats";
    let name_w = 32;
    let uses_w = 7;
    let lines_w = 11;
    let avg_lines_w = 11;
    let bytes_w = 11;
    let avg_bytes_w = 11;
    let banner_w = name_w + uses_w + lines_w + avg_lines_w + bytes_w + avg_bytes_w;

    // We write all the text into a string and print it with a single
    // `eprint!`. This is an attempt to minimize interleaved text if multiple
    // rustc processes are printing macro-stats at the same time (e.g. with
    // `RUSTFLAGS='-Zmacro-stats' cargo build`). It still doesn't guarantee
    // non-interleaving, though.
    let mut s = String::new();
    _ = writeln!(s, "{prefix} {}", "=".repeat(banner_w));
    _ = writeln!(s, "{prefix} MACRO EXPANSION STATS: {}", crate_name);
    _ = writeln!(
        s,
        "{prefix} {:<name_w$}{:>uses_w$}{:>lines_w$}{:>avg_lines_w$}{:>bytes_w$}{:>avg_bytes_w$}",
        "Macro Name", "Uses", "Lines", "Avg Lines", "Bytes", "Avg Bytes",
    );
    _ = writeln!(s, "{prefix} {}", "-".repeat(banner_w));
    // It's helpful to print something when there are no entries, otherwise it
    // might look like something went wrong.
    if macro_stats.is_empty() {
        _ = writeln!(s, "{prefix} (none)");
    }
    for (bytes, lines, uses, name, kind) in macro_stats {
        let mut name = ExpnKind::Macro(kind, *name).descr();
        let uses_with_underscores = thousands::usize_with_underscores(uses);
        let avg_lines = lines as f64 / uses as f64;
        let avg_bytes = bytes as f64 / uses as f64;

        // Ensure the "Macro Name" and "Uses" columns are as compact as possible.
        let mut uses_w = uses_w;
        if name.len() + uses_with_underscores.len() >= name_w + uses_w {
            // The name would abut or overlap the uses value. Print the name
            // on a line by itself, then set the name to empty and print things
            // normally, to show the stats on the next line.
            _ = writeln!(s, "{prefix} {:<name_w$}", name);
            name = String::new();
        } else if name.len() >= name_w {
            // The name won't abut or overlap with the uses value, but it does
            // overlap with the empty part of the uses column. Shrink the width
            // of the uses column to account for the excess name length.
            uses_w -= name.len() - name_w;
        };

        _ = writeln!(
            s,
            "{prefix} {:<name_w$}{:>uses_w$}{:>lines_w$}{:>avg_lines_w$}{:>bytes_w$}{:>avg_bytes_w$}",
            name,
            uses_with_underscores,
            thousands::usize_with_underscores(lines),
            thousands::f64p1_with_underscores(avg_lines),
            thousands::usize_with_underscores(bytes),
            thousands::f64p1_with_underscores(avg_bytes),
        );
    }
    _ = writeln!(s, "{prefix} {}", "=".repeat(banner_w));
    eprint!("{s}");
}

fn early_lint_checks(tcx: TyCtxt<'_>, (): ()) {
    let sess = tcx.sess;
    let (resolver, krate) = tcx.resolver_for_lowering();
    let resolver = &*resolver.borrow();
    let krate = &*krate.borrow();
    let mut lint_buffer = resolver.lint_buffer.steal();

    if sess.opts.unstable_opts.input_stats {
        input_stats::print_ast_stats(tcx, krate);
    }

    // Needs to go *after* expansion to be able to check the results of macro expansion.
    sess.time("complete_gated_feature_checking", || {
        rustc_ast_passes::feature_gate::check_crate(krate, sess, tcx.features());
    });

    // Add all buffered lints from the `ParseSess` to the `Session`.
    sess.psess.buffered_lints.with_lock(|buffered_lints| {
        info!("{} parse sess buffered_lints", buffered_lints.len());
        for early_lint in buffered_lints.drain(..) {
            lint_buffer.add_early_lint(early_lint);
        }
    });

    // Gate identifiers containing invalid Unicode codepoints that were recovered during lexing.
    sess.psess.bad_unicode_identifiers.with_lock(|identifiers| {
        for (ident, mut spans) in identifiers.drain(..) {
            spans.sort_by_key(|span| span.lo_hi());
            if ident == sym::ferris {
                enum FerrisFix {
                    SnakeCase,
                    ScreamingSnakeCase,
                    PascalCase,
                }

                impl FerrisFix {
                    const fn as_str(self) -> &'static str {
                        match self {
                            FerrisFix::SnakeCase => "ferris",
                            FerrisFix::ScreamingSnakeCase => "FERRIS",
                            FerrisFix::PascalCase => "Ferris",
                        }
                    }
                }

                let first_span = spans[0];
                let prev_source = sess.psess.source_map().span_to_prev_source(first_span);
                let ferris_fix = prev_source
                    .map_or(FerrisFix::SnakeCase, |source| {
                        let mut source_before_ferris = source.split_whitespace().rev();
                        match source_before_ferris.next() {
                            Some("struct" | "trait" | "mod" | "union" | "type" | "enum") => {
                                FerrisFix::PascalCase
                            }
                            Some("const" | "static") => FerrisFix::ScreamingSnakeCase,
                            Some("mut") if source_before_ferris.next() == Some("static") => {
                                FerrisFix::ScreamingSnakeCase
                            }
                            _ => FerrisFix::SnakeCase,
                        }
                    })
                    .as_str();

                sess.dcx().emit_err(diagnostics::FerrisIdentifier {
                    spans,
                    first_span,
                    ferris_fix,
                });
            } else {
                sess.dcx().emit_err(diagnostics::EmojiIdentifier { spans, ident });
            }
        }
    });

    let lint_store = unerased_lint_store(tcx.sess);
    rustc_lint::check_ast_node(
        sess,
        tcx.features(),
        false,
        lint_store,
        tcx.registered_lint_tools(()),
        Some(lint_buffer),
        EarlyCheckNode::CrateRoot(&*krate, &*krate.attrs),
    )
}

fn env_var_os<'tcx>(tcx: TyCtxt<'tcx>, key: &'tcx OsStr) -> Option<&'tcx OsStr> {
    let value = env::var_os(key);

    let value_tcx = value.as_ref().map(|value| tcx.arena.alloc_os_str(value));

    // Also add the variable to Cargo's dependency tracking
    //
    // NOTE: This only works for passes run before `write_dep_info`. See that
    // for extension points for configuring environment variables to be
    // properly change-tracked.
    tcx.sess.env_depinfo.borrow_mut().insert((
        Symbol::intern(&key.to_string_lossy()),
        value.as_ref().and_then(|value| value.to_str()).map(|value| Symbol::intern(value)),
    ));

    value_tcx
}

// Returns all the paths that correspond to generated files.
fn generated_output_paths(
    tcx: TyCtxt<'_>,
    outputs: &OutputFilenames,
    exact_name: bool,
    crate_name: Symbol,
) -> Vec<PathBuf> {
    let sess = tcx.sess;
    let mut out_filenames = Vec::new();
    for output_type in sess.opts.output_types.keys() {
        let out_filename = outputs.path(*output_type);
        let file = out_filename.as_path().to_path_buf();
        match *output_type {
            // If the filename has been overridden using `-o`, it will not be modified
            // by appending `.rlib`, `.exe`, etc., so we can skip this transformation.
            OutputType::Exe if !exact_name => {
                for crate_type in tcx.crate_types().iter() {
                    let p = filename_for_input(sess, *crate_type, crate_name, outputs);
                    out_filenames.push(p.as_path().to_path_buf());
                }
            }
            OutputType::DepInfo if sess.opts.unstable_opts.dep_info_omit_d_target => {
                // Don't add the dep-info output when omitting it from dep-info targets
            }
            OutputType::DepInfo if out_filename.is_stdout() => {
                // Don't add the dep-info output when it goes to stdout
            }
            _ => {
                out_filenames.push(file);
            }
        }
    }
    out_filenames
}

fn output_contains_path(output_paths: &[PathBuf], input_path: &Path) -> bool {
    let input_path = try_canonicalize(input_path).ok();
    if input_path.is_none() {
        return false;
    }
    output_paths.iter().any(|output_path| try_canonicalize(output_path).ok() == input_path)
}

fn output_conflicts_with_dir(output_paths: &[PathBuf]) -> Option<&PathBuf> {
    output_paths.iter().find(|output_path| output_path.is_dir())
}

// Trust: capture the existing dependency data without retaining TyCtxt or Session.
// The opted-in terminal writer can retain this carrier beyond TyCtxt.
fn prepare_dep_info(
    tcx: TyCtxt<'_>,
    destination: OutFileName,
    out_filenames: &[PathBuf],
) -> PreparedDepInfo {
    let sess = tcx.sess;
    // Build a list of files used to compile the output and
    // write Makefile-compatible dependency rules
    let mut files: IndexMap<String, (u64, Option<SourceFileHash>)> = sess
        .source_map()
        .files()
        .iter()
        .filter(|fmap| fmap.is_real_file())
        .filter(|fmap| !fmap.is_imported())
        .map(|fmap| {
            (
                escape_dep_filename(fmap.name.prefer_local_unconditionally().to_string()),
                (
                    // This needs to be unnormalized,
                    // as external tools wouldn't know how rustc normalizes them
                    fmap.unnormalized_source_len as u64,
                    fmap.checksum_hash,
                ),
            )
        })
        .collect();

    let checksum_hash_algo = sess.opts.unstable_opts.checksum_hash_algorithm;

    // Account for explicitly marked-to-track files
    // (e.g. accessed in proc macros).
    let file_depinfo = sess.file_depinfo.borrow();

    // The entries will be used to declare dependencies between files in a
    // Makefile-like output, so the iteration order does not matter.
    // Trust: hash the raw filesystem path and escape only its emitted dep-info key.
    // Escaped spaces are Makefile syntax, not characters in the filename to open.
    fn hash_iter_files<P: AsRef<Path>>(
        it: impl Iterator<Item = P>,
        checksum_hash_algo: Option<SourceFileHashAlgorithm>,
    ) -> impl Iterator<Item = (String, (u64, Option<SourceFileHash>))> {
        it.map(move |path| {
            let checksum = checksum_hash_algo.and_then(|algo| {
                fs::File::open(path.as_ref())
                    .and_then(|mut file| SourceFileHash::new(algo, &mut file).map(|h| (file, h)))
                    .and_then(|(file, h)| file.metadata().map(|m| (m.len(), h)))
                    .map_err(|e| {
                        tracing::error!(
                            "failed to compute checksum, omitting it from dep-info {} {e}",
                            path.as_ref().display()
                        )
                    })
                    .ok()
            });
            let key = escape_dep_filename(path.as_ref().to_string_lossy());
            (
                key,
                match checksum {
                    Some((file_len, checksum)) => (file_len, Some(checksum)),
                    None => (0, None),
                },
            )
        })
    }

    // Trust: all hash_iter_files callers pass raw paths; the helper owns output escaping.
    let extra_tracked_files = hash_iter_files(
        file_depinfo.iter().map(|path_sym| Path::new(path_sym.as_str())),
        checksum_hash_algo,
    );
    files.extend(extra_tracked_files);

    // We also need to track used PGO profile files
    if let Some(ref profile_instr) = sess.opts.cg.profile_use {
        files.extend(hash_iter_files(iter::once(profile_instr.as_path()), checksum_hash_algo));
    }
    if let Some(ref profile_sample) = sess.opts.cg.profile_sample_use {
        files.extend(hash_iter_files(iter::once(profile_sample.as_path()), checksum_hash_algo));
    }

    // Debugger visualizer files
    for debugger_visualizer in tcx.debugger_visualizers(LOCAL_CRATE) {
        files.extend(hash_iter_files(
            iter::once(debugger_visualizer.path.clone().unwrap()),
            checksum_hash_algo,
        ));
    }

    if sess.binary_dep_depinfo() {
        if let Some(ref backend) = sess.opts.unstable_opts.codegen_backend {
            if backend.contains('.') {
                // If the backend name contain a `.`, it is the path to an external dynamic
                // library. If not, it is not a path.
                files.extend(hash_iter_files(iter::once(backend.to_string()), checksum_hash_algo));
            }
        }

        for &cnum in tcx.crates(()) {
            let source = tcx.used_crate_source(cnum);
            if let Some(path) = &source.dylib {
                files.extend(hash_iter_files(iter::once(path), checksum_hash_algo));
            }
            if let Some(path) = &source.rlib {
                files.extend(hash_iter_files(iter::once(path), checksum_hash_algo));
            }
            if let Some(path) = &source.rmeta {
                files.extend(hash_iter_files(iter::once(path), checksum_hash_algo));
            }
        }
    }

    // Trust: this crate's potential managed cache belongs to its out-dir.
    // An explicit caller-selected witness path is never exposed to package clean.
    let managed_witness =
        sess.io.output_dir.is_some().then(|| tcx.stable_crate_id(LOCAL_CRATE).as_u64());
    // Trust: escape and own environment rows before the query context ends.
    // The canonical formatter sorts these exact escaped rows as before.
    let env_depinfo = sess.env_depinfo.borrow();
    #[allow(rustc::potential_query_instability)]
    let envs = env_depinfo
        .iter()
        .map(|(key, value)| {
            (escape_dep_env(key.as_str()), value.map(|value| escape_dep_env(value.as_str())))
        })
        .collect();
    PreparedDepInfo::new(
        destination,
        out_filenames.to_vec(),
        files,
        envs,
        managed_witness,
        checksum_hash_algo.is_some(),
    )
}

// Trust: one publication path; notify only after the complete checked flush.
pub fn finish_dep_info(sess: &Session, mut prepared: PreparedDepInfo) {
    prepared.set_tool_inputs(sess.terminal_tool_inputs());
    let deps_filename = prepared.destination();
    match prepared.write() {
        Ok(_) => {
            if sess.opts.json_artifact_notifications {
                sess.dcx().emit_artifact_notification(deps_filename, "dep-info");
            }
        }
        Err(error) => {
            sess.dcx()
                .emit_fatal(diagnostics::ErrorWritingDependencies { path: deps_filename, error });
        }
    }
}

fn resolver_for_lowering_raw<'tcx>(
    tcx: TyCtxt<'tcx>,
    (): (),
) -> (&'tcx Steal<ResolverAstLowering<'tcx>>, &'tcx Steal<ast::Crate>, &'tcx ResolverGlobalCtxt) {
    let arenas = WorkerLocal::new(|_| Resolver::arenas());
    let _ = tcx.registered_attr_tools(()); // Uses `crate_for_resolver`.
    let _ = tcx.registered_lint_tools(()); // Uses `crate_for_resolver`.
    let (krate, pre_configured_attrs) = tcx.crate_for_resolver(()).steal();
    let mut resolver = Resolver::new(
        tcx,
        &pre_configured_attrs,
        krate.spans.inner_span,
        krate.spans.inject_use_span,
        &arenas,
    );
    let krate = configure_and_expand(krate, &pre_configured_attrs, &mut resolver);

    // Don't mutate the cstore or stable crate id map from here on.
    tcx.untracked().freeze_cstore();

    let ResolverOutputs {
        global_ctxt: untracked_resolutions,
        ast_lowering: untracked_resolver_for_lowering,
    } = resolver.into_outputs();

    (
        tcx.arena.alloc(Steal::new(untracked_resolver_for_lowering)),
        tcx.arena.alloc(Steal::new(krate)),
        tcx.arena.alloc(untracked_resolutions),
    )
}

pub fn write_dep_info(tcx: TyCtxt<'_>) {
    // Trust: pretty/dependency-only/no-analysis and other early exits preserve
    // their original emission point, but cannot report a completed link unit.
    tcx.sess.tool_inputs_unavailable();
    let _ = dep_info_inner(tcx, false);
}

// Trust: prepare owned data while query-dependent hashes are still available.
// Output safety checks and directory creation keep their original order.
pub fn prepare_dep_info_for_link(tcx: TyCtxt<'_>) -> Option<PreparedDepInfo> {
    dep_info_inner(tcx, true)
}

fn dep_info_inner(tcx: TyCtxt<'_>, defer: bool) -> Option<PreparedDepInfo> {
    // Make sure name resolution and macro expansion is run for
    // the side-effect of providing a complete set of all
    // accessed files and env vars.
    let _ = tcx.resolver_for_lowering();

    let sess = tcx.sess;
    let _timer = sess.timer("write_dep_info");
    let crate_name = tcx.crate_name(LOCAL_CRATE);

    let outputs = tcx.output_filenames(());
    let output_paths =
        generated_output_paths(tcx, outputs, sess.io.output_file.is_some(), crate_name);

    // Ensure the source file isn't accidentally overwritten during compilation.
    if let Some(input_path) = sess.io.input.opt_path() {
        if sess.opts.will_create_output_file() {
            if output_contains_path(&output_paths, input_path) {
                sess.dcx()
                    .emit_fatal(diagnostics::InputFileWouldBeOverWritten { path: input_path });
            }
            if let Some(dir_path) = output_conflicts_with_dir(&output_paths) {
                sess.dcx().emit_fatal(diagnostics::GeneratedFileConflictsWithDirectory {
                    input_path,
                    dir_path,
                });
            }
        }
    }

    if let Some(ref dir) = sess.io.temps_dir {
        if fs::create_dir_all(dir).is_err() {
            sess.dcx().emit_fatal(diagnostics::TempsDirError);
        }
    }

    // Trust: only explicitly opted-in normal compilation delays publication.
    let prepared = sess
        .opts
        .output_types
        .contains_key(&OutputType::DepInfo)
        .then(|| prepare_dep_info(tcx, outputs.path(OutputType::DepInfo), &output_paths));
    let deferred = if defer {
        prepared
    } else {
        if let Some(prepared) = prepared {
            finish_dep_info(sess, prepared);
        }
        None
    };

    let only_dep_info = sess.opts.output_types.contains_key(&OutputType::DepInfo)
        && sess.opts.output_types.len() == 1;

    if !only_dep_info {
        if let Some(ref dir) = sess.io.output_dir {
            if fs::create_dir_all(dir).is_err() {
                sess.dcx().emit_fatal(diagnostics::OutDirError);
            }
        }
    }
    deferred
}

pub fn write_interface<'tcx>(tcx: TyCtxt<'tcx>) {
    if !tcx.crate_types().contains(&rustc_structures::CrateType::Sdylib) {
        return;
    }
    let _timer = tcx.sess.timer("write_interface");
    let (_, krate) = tcx.resolver_for_lowering();

    let krate = rustc_ast_pretty::pprust::print_crate_as_interface(
        &*krate.borrow(),
        tcx.sess.psess.edition,
        &tcx.sess.psess.attr_id_generator,
    );
    let export_output = tcx.output_filenames(()).interface_path();
    let mut file = fs::File::create_buffered(&export_output).unwrap_or_else(|error| {
        tcx.dcx().emit_fatal(diagnostics::FailedWritingFile { path: &export_output, error })
    });
    if let Err(error) = write!(file, "{}", krate) {
        tcx.dcx().emit_fatal(diagnostics::FailedWritingFile { path: &export_output, error });
    }
}

pub static DEFAULT_QUERY_PROVIDERS: LazyLock<Providers> = LazyLock::new(|| {
    let providers = &mut Providers::default();
    providers.queries.analysis = analysis;
    providers.queries.resolver_for_lowering_raw = resolver_for_lowering_raw;
    providers.queries.stripped_cfg_items = |tcx, _| &tcx.resolutions(()).stripped_cfg_items[..];
    providers.queries.get_lang_items = |tcx, ()| &tcx.resolutions(()).lang_items;
    providers.queries.resolutions = |tcx, ()| tcx.resolver_for_lowering_raw(()).2;
    providers.queries.early_lint_checks = early_lint_checks;
    providers.queries.env_var_os = env_var_os;
    providers.queries.proc_macro_decls_static = |tcx, _| tcx.hir_crate_items(()).proc_macro_decls();
    rustc_ast_lowering::provide(&mut providers.queries);
    rustc_expand_queries::provide(&mut providers.queries);
    rustc_const_eval::provide(providers);
    rustc_middle::hir::provide(&mut providers.queries);
    rustc_borrowck::provide(&mut providers.queries);
    rustc_incremental::provide(providers);
    rustc_mir_build::provide(providers);
    rustc_mir_dataflow::provide(providers);
    rustc_mir_transform::provide(providers);
    rustc_monomorphize::provide(providers);
    rustc_privacy::provide(&mut providers.queries);
    rustc_query_impl::provide(providers);
    rustc_resolve::provide(&mut providers.queries);
    rustc_hir_analysis::provide(&mut providers.queries);
    rustc_hir_typeck::provide(&mut providers.queries);
    ty::provide(&mut providers.queries);
    traits::provide(&mut providers.queries);
    solve::provide(&mut providers.queries);
    rustc_passes::provide(&mut providers.queries);
    rustc_traits::provide(&mut providers.queries);
    rustc_ty_utils::provide(&mut providers.queries);
    rustc_metadata::provide(providers);
    rustc_lint::provide(&mut providers.queries);
    rustc_symbol_mangling::provide(&mut providers.queries);
    rustc_codegen_ssa::provide(providers);
    *providers
});

/// Trust's whole-crate coverage and proof semantics are anchored in the
/// canonical analysis, AST-to-HIR lowering and attribute inventory, HIR/THIR/MIR
/// construction pipeline, runtime/link closure, type and layout inputs,
/// contracts, and proof-result providers. Proof-active query callbacks are
/// rejected wholesale below; this exact-provider boundary also defends against
/// providers installed by the selected codegen backend. Replacing any provider
/// in this transitive chain can shrink an authenticated run to a successful 0/0
/// inventory, hide an unauthenticated startup surface, verify a synthetic body
/// or type universe instead of the one rustc constructed, suppress
/// borrow-checking, delete contract obligations, or inject fabricated proof
/// evidence.
fn changed_trust_critical_query_provider(providers: &Providers) -> Option<&'static str> {
    let canonical = &*DEFAULT_QUERY_PROVIDERS;

    macro_rules! reject_changed_query {
        ($field:ident) => {
            if !std::ptr::fn_addr_eq(providers.queries.$field, canonical.queries.$field) {
                return Some(stringify!($field));
            }
        };
    }

    macro_rules! reject_changed_extern_query {
        ($field:ident) => {
            if !std::ptr::fn_addr_eq(
                providers.extern_queries.$field,
                canonical.extern_queries.$field,
            ) {
                return Some(concat!("extern::", stringify!($field)));
            }
        };
    }

    reject_changed_query!(analysis);
    reject_changed_query!(crates);
    reject_changed_query!(dependency_formats);
    reject_changed_query!(exported_generic_symbols);
    reject_changed_query!(exported_non_generic_symbols);
    reject_changed_query!(foreign_modules);
    reject_changed_query!(hir_attr_map);
    reject_changed_query!(hir_crate_items);
    // Trust: owner-node, body and trait-map reads go through this projection
    // provider even when the original lower_to_hir provider is unchanged.
    reject_changed_query!(hir_owner);
    reject_changed_query!(has_alloc_error_handler);
    reject_changed_query!(has_global_allocator);
    reject_changed_query!(has_panic_handler);
    reject_changed_query!(index_ast);
    reject_changed_query!(lower_to_hir);
    reject_changed_query!(thir_body);
    reject_changed_query!(typeck_root);
    reject_changed_query!(closure_typeinfo);
    reject_changed_query!(mir_keys);
    reject_changed_query!(mir_built);
    reject_changed_query!(mir_borrowck);
    reject_changed_query!(mir_const_qualif);
    reject_changed_query!(mir_promoted);
    reject_changed_query!(mir_drops_elaborated_and_const_checked);
    reject_changed_query!(mir_for_ctfe);
    reject_changed_query!(optimized_mir);
    reject_changed_query!(native_libraries);
    reject_changed_query!(resolver_for_lowering_raw);

    // Direct TrustIR seed queries and the high-confidence transitive inputs
    // used by THIR lowering, type conversion, constant evaluation, and body
    // identity. The query-level names below are the provider seams behind
    // wrapper methods such as `closure_captures`,
    // `const_eval_resolve_for_typeck`, `type_is_copy_modulo_regions`, and
    // `try_normalize_erasing_regions`.
    reject_changed_query!(type_of);
    reject_changed_query!(fn_sig);
    reject_changed_query!(generics_of);
    reject_changed_query!(layout_of);
    reject_changed_query!(eval_to_const_value_raw);
    reject_changed_query!(resolve_instance_raw);
    reject_changed_query!(adt_def);
    reject_changed_query!(param_env);
    reject_changed_query!(region_scope_tree);
    reject_changed_query!(symbol_name);
    reject_changed_query!(associated_item);
    reject_changed_query!(impl_trait_header);
    reject_changed_query!(codegen_fn_attrs);
    reject_changed_query!(coroutine_for_closure);
    reject_changed_query!(coroutine_kind);
    reject_changed_query!(crate_name);
    reject_changed_query!(def_kind);
    reject_changed_query!(def_span);
    reject_changed_query!(fn_arg_idents);
    reject_changed_query!(attrs_for_def);
    reject_changed_query!(get_lang_items);
    reject_changed_query!(defined_lang_items);
    reject_changed_query!(diagnostic_items);
    reject_changed_query!(intrinsic_raw);
    reject_changed_query!(is_copy_raw);
    reject_changed_query!(try_normalize_generic_arg_after_erasing_regions);
    reject_changed_query!(trust_contracts);
    reject_changed_query!(trust_proof_results);
    // Trust: D4 increment A (2026-09-24) — the user-`unsafe` source fact gates
    // re-derivation of a dependency body; a callback must not be able to answer it.
    reject_changed_query!(trust_def_has_user_unsafe_source);
    reject_changed_extern_query!(trust_def_has_user_unsafe_source);
    // Trust: CB3 (2026-09-28) — the per-def island marker exempts a
    // `DefKind::GlobalAsm` def from the certified-monitor startup-surface
    // refusal; a callback answering `true` would admit real `global_asm!`.
    reject_changed_query!(trust_def_is_clean_island);
    reject_changed_extern_query!(trust_def_is_clean_island);
    // Trust: PKG-C5d — the spawn census's sysroot scan reads each sysroot body's
    // `mentioned_items` through this query; a callback answering `None` would close
    // `dyn` pools short (a missing spawn row) without disturbing codegen.
    reject_changed_query!(trust_mentioned_items);
    reject_changed_extern_query!(trust_mentioned_items);
    reject_changed_query!(codegen_fn_attrs);
    reject_changed_extern_query!(codegen_fn_attrs);
    reject_changed_extern_query!(crate_dep_kind);
    reject_changed_extern_query!(def_kind);
    reject_changed_extern_query!(dylib_dependency_formats);
    reject_changed_extern_query!(exported_generic_symbols);
    reject_changed_extern_query!(exported_non_generic_symbols);
    // The loader's record of HOW a crate entered the graph — which `--extern`
    // item or injected `extern crate` named it, and where. Trust's sysroot
    // identity rule does NOT read it: identity is artifact residency
    // (`used_crate_source`, listed below) plus a command-line flag, deliberately,
    // because a 2026-08-21 rule that DID read this record was refuted the same
    // day — the injected item resolves through the adversary-controlled
    // `--extern` map, so the record says which crate landed in the slot, not that
    // the compiler chose it (`trust_mir_extract::convert::
    // impersonates_sysroot_crate` carries the measurement). It stays on this list
    // anyway: the list is the set of loader/provenance records a driver callback
    // must not be able to fabricate, and this is one of them. MEASURED: zero
    // call sites under `crates/` read it today (one prose mention, no call) —
    // grep before assuming otherwise.
    reject_changed_extern_query!(extern_crate);
    reject_changed_extern_query!(has_alloc_error_handler);
    reject_changed_extern_query!(has_global_allocator);
    reject_changed_extern_query!(has_panic_handler);
    reject_changed_extern_query!(is_compiler_builtins);
    reject_changed_extern_query!(is_panic_runtime);
    reject_changed_extern_query!(is_profiler_runtime);
    reject_changed_extern_query!(native_libraries);
    reject_changed_extern_query!(num_extern_def_ids);
    reject_changed_extern_query!(panic_in_drop_strategy);
    reject_changed_extern_query!(required_panic_strategy);
    reject_changed_extern_query!(used_crate_source);

    // The same semantic inputs for referenced upstream definitions must be
    // canonical as well; otherwise a callback can preserve the local body and
    // spoof the signatures, attributes, or identities of its callees.
    reject_changed_extern_query!(type_of);
    reject_changed_extern_query!(fn_sig);
    reject_changed_extern_query!(generics_of);
    reject_changed_extern_query!(adt_def);
    reject_changed_extern_query!(associated_item);
    reject_changed_extern_query!(impl_trait_header);
    reject_changed_extern_query!(codegen_fn_attrs);
    reject_changed_extern_query!(coroutine_for_closure);
    reject_changed_extern_query!(coroutine_kind);
    reject_changed_extern_query!(crate_name);
    reject_changed_extern_query!(def_kind);
    reject_changed_extern_query!(def_span);
    reject_changed_extern_query!(fn_arg_idents);
    reject_changed_extern_query!(attrs_for_def);
    reject_changed_extern_query!(defined_lang_items);
    reject_changed_extern_query!(diagnostic_items);
    reject_changed_extern_query!(intrinsic_raw);

    if !std::ptr::fn_addr_eq(
        providers.hooks.build_mir_inner_impl,
        canonical.hooks.build_mir_inner_impl,
    ) {
        return Some("build_mir_inner_impl");
    }
    if !std::ptr::fn_addr_eq(
        providers.hooks.try_destructure_mir_constant_for_user_output,
        canonical.hooks.try_destructure_mir_constant_for_user_output,
    ) {
        return Some("try_destructure_mir_constant_for_user_output");
    }
    None
}

fn trust_critical_provider_violation(
    providers: &Providers,
    trust_semantics_active: bool,
) -> Option<&'static str> {
    trust_semantics_active.then(|| changed_trust_critical_query_provider(providers)).flatten()
}

fn query_override_callback_conflicts(
    callback_registered: bool,
    trust_semantics_active: bool,
) -> bool {
    callback_registered && trust_semantics_active
}

pub fn create_and_enter_global_ctxt<T, F: for<'tcx> FnOnce(TyCtxt<'tcx>) -> T>(
    compiler: &Compiler,
    krate: rustc_ast::Crate,
    f: F,
) -> (T, Option<IncrCompSession>) {
    let sess = &compiler.sess;

    let pre_configured_attrs = rustc_expand::config::pre_configure_attrs(sess, &krate.attrs);

    let crate_name = get_crate_name(sess, &pre_configured_attrs);
    let crate_types = collect_crate_types(
        sess,
        &compiler.codegen_backend.supported_crate_types(sess),
        compiler.codegen_backend.name(),
        compiler.codegen_backend.unsupported_crate_type_is_fatal(sess),
        &pre_configured_attrs,
        krate.spans.inner_span,
    );
    let stable_crate_id = StableCrateId::new(
        crate_name,
        crate_types.contains(&CrateType::Executable),
        sess.opts.cg.metadata.clone(),
        sess.cfg_version,
    );

    let outputs = util::build_output_filenames(&pre_configured_attrs, sess);

    let (dep_graph, incr_comp_session) = setup_dep_graph(sess, crate_name, stable_crate_id);

    let cstore =
        FreezeLock::new(Box::new(CStore::new(compiler.codegen_backend.metadata_loader())) as _);
    let definitions = FreezeLock::new(Definitions::new(stable_crate_id));

    let stable_crate_ids = FreezeLock::new(StableCrateIdMap::default());
    let untracked = Untracked {
        cstore,
        source_span: AppendOnlyIndexVec::new(),
        definitions,
        stable_crate_ids,
        local_crate_hash: OnceLock::new(),
    };

    // We're constructing the HIR here; we don't care what we will
    // read, since we haven't even constructed the *input* to
    // incr. comp. yet.
    dep_graph.assert_ignored();

    let query_result_on_disk_cache =
        rustc_incremental::load_query_result_cache(sess, incr_comp_session.as_ref());

    let codegen_backend = &compiler.codegen_backend;
    #[allow(rustc::bad_opt_access)]
    let trust_query_semantics_active = sess.trust_verification_enabled()
        || sess.trust_ir_lower_enabled()
        || sess.opts.unstable_opts.trust_targo_test_monitor
        || sess.opts.unstable_opts.trust_certified_test_monitors;
    if query_override_callback_conflicts(
        compiler.override_queries.is_some(),
        trust_query_semantics_active,
    ) {
        sess.dcx().fatal(
            "Config::override_queries is not permitted while Trust verification or direct TrustIR lowering is active; proof semantics require compiler-owned query providers",
        );
    }

    let mut providers = *DEFAULT_QUERY_PROVIDERS;
    codegen_backend.provide(&mut providers);

    if let Some(callback) = compiler.override_queries {
        callback(sess, &mut providers);
    }

    if let Some(query) = trust_critical_provider_violation(&providers, trust_query_semantics_active)
    {
        sess.dcx().fatal(format!(
            "compiler callback or codegen backend replaced Trust-critical provider `{query}`; Trust analysis requires the canonical analysis, HIR/MIR inventory and body pipeline, contract, and proof-result providers"
        ));
    }

    let incremental = dep_graph.is_fully_enabled();
    let track_present = incremental
        || sess.opts.unstable_opts.incremental_verify_ich
        || sess.prof.enabled()
        || cfg!(debug_assertions);

    // Note: this function body is the origin point of the widely-used 'tcx lifetime.
    //
    // `gcx_cell` is defined here and `&gcx_cell` is passed to `create_global_ctxt`, which then
    // actually creates the `GlobalCtxt` with a `gcx_cell.get_or_init(...)` call. This is done so
    // that the resulting reference has the type `&'tcx GlobalCtxt<'tcx>`, which is what `TyCtxt`
    // needs. If we defined and created the `GlobalCtxt` within `create_global_ctxt` then its type
    // would be `&'a GlobalCtxt<'tcx>`, with two lifetimes.
    //
    // Similarly, by creating `arena` here and passing in `&arena`, that reference has the type
    // `&'tcx WorkerLocal<Arena<'tcx>>`, also with one lifetime. And likewise for `hir_arena`.

    let gcx_cell = OnceLock::new();
    let arena = WorkerLocal::new(|_| Arena::default());
    let hir_arena = WorkerLocal::new(|_| rustc_hir::Arena::default());

    let res = TyCtxt::create_global_ctxt(
        &gcx_cell,
        &compiler.sess,
        crate_types,
        stable_crate_id,
        &arena,
        &hir_arena,
        untracked,
        incr_comp_session.as_ref(),
        dep_graph,
        rustc_query_impl::query_system(
            &arena,
            providers.queries,
            providers.extern_queries,
            query_result_on_disk_cache,
            incremental,
            track_present,
        ),
        providers.hooks,
        compiler.current_gcx.clone(),
        |tcx| {
            let feed = tcx.create_crate_num(stable_crate_id).unwrap();
            assert_eq!(feed.key(), LOCAL_CRATE);
            feed.crate_name(crate_name);

            let feed = tcx.feed_unit_query();
            let features = tcx.arena.alloc(rustc_expand::config::features(
                tcx.sess,
                &pre_configured_attrs,
                crate_name,
            ));
            feed.features_query(features);
            feed.limits(limits::get_limits(&pre_configured_attrs, tcx.sess, features));
            feed.crate_for_resolver(tcx.arena.alloc(Steal::new((krate, pre_configured_attrs))));
            feed.output_filenames(Arc::new(outputs));

            // There are two paths out of `f`.
            // - Normal exit.
            // - Panic, e.g. triggered by `abort_if_errors` or a fatal error.
            //
            // If a panic occurs, we still need to wind down the self-profiler to correctly record
            // the query events that are still in flight. Otherwise, they will be invalid and will
            // show up as "<unknown>" in the profiling data.
            let res = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| f(tcx)));
            let res = match res {
                Ok(res) => res,
                Err(err) => {
                    tcx.alloc_self_profile_query_strings();

                    // Resume unwinding if a panic happened.
                    std::panic::resume_unwind(err);
                }
            };
            // Emit only after the crate callback completed successfully. A
            // panicking/fatal compilation has no complete authenticated
            // coverage inventory to publish.
            rustc_mir_transform::trust_emit_transport_crate_summary(tcx);
            tcx.finish();
            res
        },
    );

    (res, incr_comp_session)
}

struct DiagCallback<'tcx> {
    callback: Box<
        dyn for<'b> FnOnce(DiagCtxtHandle<'b>, Level, &dyn Any) -> Diag<'b> + DynSend + DynSync,
    >,
    tcx: TyCtxt<'tcx>,
}

impl<'a, 'tcx> Diagnostic<'a> for DiagCallback<'tcx> {
    fn into_diag(self, dcx: DiagCtxtHandle<'a>, level: Level) -> Diag<'a> {
        (self.callback)(dcx, level, self.tcx.sess)
    }
}

// Trust (TG3, COMPILE-TIME-FACTS-1): rustdoc runs no `analysis`, so it reaches
// the crate's Clean islands and kernel obligations only through this entry.
pub fn trust_check_kernel_obligations_for_rustdoc(tcx: TyCtxt<'_>) {
    rustc_mir_transform::trust_check_kernel_obligations_for_rustdoc(tcx);
}

pub fn emit_delayed_lints(tcx: TyCtxt<'_>) {
    for owner_id in tcx.hir_crate_items(()).owners() {
        if let Some(delayed_lints) = tcx.opt_ast_lowering_delayed_lints(owner_id) {
            for lint in delayed_lints.steal() {
                tcx.emit_node_span_lint(
                    lint.lint_id.lint,
                    lint.id,
                    lint.span.clone(),
                    DiagCallback { callback: lint.callback, tcx },
                );
            }
        }
    }
}

/// Runs all analyses that we guarantee to run, even if errors were reported in earlier analyses.
/// This function never fails.
fn run_required_analyses(tcx: TyCtxt<'_>) {
    if tcx.sess.opts.unstable_opts.input_stats {
        rustc_passes::input_stats::print_hir_stats(tcx);
    }
    // When using rustdoc's "jump to def" feature, it enters this code and `check_crate`
    // is not defined. So we need to cfg it out.
    #[cfg(all(not(doc), debug_assertions))]
    rustc_passes::hir_id_validator::check_crate(tcx);

    // Prefetch this to prevent multiple threads from blocking on it later.
    // This is needed since the `hir_id_validator::check_crate` call above is not guaranteed
    // to use `hir_crate_items`.
    tcx.ensure_done().hir_crate_items(());

    tcx.untracked().definitions.write().commit_end_of_determinism();

    rustc_passes::delegation::check_glob_and_list_delegations_target_expr(tcx);

    let sess = tcx.sess;
    sess.time("misc_checking_1", || {
        par_fns(&mut [
            &mut || {
                sess.time("looking_for_entry_point", || tcx.ensure_ok().entry_fn(()));
                sess.time("check_externally_implementable_items", || {
                    tcx.ensure_ok().check_externally_implementable_items(())
                });

                sess.time("looking_for_derive_registrar", || {
                    tcx.ensure_ok().proc_macro_decls_static(())
                });

                CStore::from_tcx(tcx).report_unused_deps(tcx);
            },
            &mut || {
                tcx.ensure_ok().exportable_items(LOCAL_CRATE);
                tcx.ensure_ok().stable_order_of_exportable_impls(LOCAL_CRATE);
                tcx.par_hir_for_each_module(|module| {
                    tcx.ensure_ok().check_mod_attrs(module);
                    tcx.ensure_ok().check_mod_unstable_api_usage(module);
                });
            },
        ]);
    });

    sess.time("emit_ast_lowering_delayed_lints", || {
        emit_delayed_lints(tcx);
    });

    rustc_hir_analysis::check_crate(tcx);
    // Freeze definitions as we don't add new ones at this point.
    // We need to wait until now since we synthesize a by-move body
    // for all coroutine-closures.
    //
    // This improves performance by allowing lock-free access to them.
    tcx.untracked().definitions.freeze();

    // This independent HIR roster includes the generated by-move coroutine
    // bodies introduced by type checking. No producer registry is consulted.
    crate::trust_body_census::snapshot(tcx);

    sess.time("MIR_borrow_checking", || {
        tcx.par_hir_body_owners(|def_id| {
            // Trivial consts don't involve `unsafe` so we can check this before `check_unsafety`.
            if tcx.is_trivial_const(def_id) {
                return;
            }
            let not_typeck_child = !tcx.is_typeck_child(def_id.to_def_id());
            if not_typeck_child {
                // Child unsafety and borrowck happens together with the parent
                tcx.ensure_ok().check_unsafety(def_id);
            }
            // Trust (deferred-verification lane, Step 3): on the trust-ir artifact
            // lane, the REJECTION-only analyses are deferred to the verifier stage
            // that consumes the artifact (trust-vc owns ownership/borrow
            // verification on trust-ir). USER-AUTHORIZED, lane-scoped, recorded in
            // the artifact provenance; every other lane takes the branch below
            // unchanged.
            //
            // `check_unsafety` above STAYS: it is the compiler's only THIR reclaim
            // point (its `thir.steal()`), and it drives the producer's hook for
            // closures/inline-consts via `visit_inner_body`.
            if tcx.trust_defer_verification() {
                // BLOCKING: `check_unsafety` early-returns for `#[custom_mir]`
                // bodies BEFORE its `mir_built` force, so today those bodies reach
                // the producer only via `mir_borrowck -> mir_promoted`. Deferring
                // borrowck without this explicit force would silently DROP them
                // (and any closure nested in them) from the artifact — a wrong
                // artifact, which this program ranks strictly worse than a slow
                // one. `library/core` contains such bodies.
                tcx.ensure_done().mir_built(def_id);
            } else {
                if not_typeck_child {
                    tcx.ensure_ok().mir_borrowck(def_id);
                    tcx.ensure_ok().check_transmutes(def_id);
                    if !tcx.sess.opts.unstable_opts.offload.is_empty() {
                        tcx.ensure_ok().check_offloads(def_id);
                    }
                }
                tcx.ensure_ok().has_ffi_unwind_calls(def_id);
                tcx.ensure_ok().check_liveness(def_id);
            }

            // If we need to codegen, ensure that we emit all errors from
            // `mir_drops_elaborated_and_const_checked` now, to avoid discovering
            // them later during codegen.
            if tcx.sess.opts.output_types.should_codegen()
                || tcx.hir_body_const_context(def_id).is_some()
            {
                tcx.ensure_ok().mir_drops_elaborated_and_const_checked(def_id);
            }
            if tcx.is_coroutine(def_id.to_def_id())
                && (!tcx.is_async_drop_in_place_coroutine(def_id.to_def_id()))
            {
                // Eagerly check the unsubstituted layout for cycles.
                tcx.ensure_ok()
                    .layout_of(ty::TypingEnv::codegen(tcx, def_id.to_def_id()).as_query_input(
                        tcx.type_of(def_id).instantiate_identity().skip_norm_wip(),
                    ));
            }
        });
    });

    sess.time("layout_testing", || layout_test::test_layout(tcx));
    sess.time("abi_testing", || abi_test::test_abi(tcx));
}

/// Runs the type-checking, region checking and other miscellaneous analysis
/// passes on the crate.
fn analysis(tcx: TyCtxt<'_>, (): ()) {
    run_required_analyses(tcx);

    // Trust (scope-truncation fix): snapshot the front-end error state BEFORE the
    // trust analysis-seam hooks below run. Those hooks demand `optimized_mir` — and
    // with it the TrustVerify pass, which may emit verification ERRORs — for an
    // ordering-dependent subset of bodies, so an error present HERE is a genuine
    // front-end error, while an error first appearing after this point is a trust
    // verification verdict. The eager whole-crate verification walk below runs only
    // on a front-end-clean crate: optimizing MIR of code that failed type/borrow
    // checking is ICE-prone (see the `-Zvalidate-mir` note at the end of this
    // function), and verification coverage of a crate that cannot compile is moot —
    // the `has_errors_excluding_lint_errors` gate below keeps its exact behavior for
    // that case.
    let front_end_errors_before_trust_hooks = tcx.sess.dcx().has_errors_excluding_lint_errors();

    // Trust: the two whole-crate seam initializers below run only on a
    // front-end-clean crate, like the eager verification walk that consumes
    // their results: on an erroring crate the fatal gate below aborts before
    // codegen ever runs TrustVerify, so the whole-crate extraction + R1 SMT
    // harvest would be pure wasted work (and optimizing MIR of code that
    // failed type/borrow checking is ICE-prone).
    if front_end_errors_before_trust_hooks.is_none() {
        // Trust (CORE3): prepare the one fixed mathematical base before the
        // following initializer demands can start per-function verification
        // clocks. Self-gates on verification, production pins and hint root;
        // setup keeps genuine inherited stops and earns no function credit.
        rustc_mir_transform::trust_init_calculus_reporting(tcx);
        // Trust (2026-09-29): force the crate call-graph oracles (the mutual-recursion
        // SCC set and the transitive spawn census) HERE, at one fixed program point:
        // `run_required_analyses` is done, no query is active, and — with verification
        // enabled — no fn, closure or coroutine body has been stolen (a coroutine's
        // layout is read pre-steal, `trust_local_coroutine_layout`). They used to be
        // forced by the first `optimized_mir`, which a coroutine layout could demand from
        // inside type computation. `inner_optimized_mir` keeps its forces as a fallback.
        // Self-gates on verification being enabled.
        rustc_mir_transform::trust_force_crate_graph_oracles(tcx);
        // Trust: the once-initializer re-entrancy check — a `OnceLock`/`LazyLock`/
        // `Once` (or `OnceCell`/`LazyCell`) `static` whose initializer can wait on
        // its own cell is a HARD error (aterm v0.65.0's update-apply deadlock,
        // 2026-08-30). It runs FIRST here because it borrows
        // `mir_drops_elaborated_and_const_checked`, which the backing-certificate
        // initializer below STEALS through `optimized_mir`; and it is gated by
        // NOTHING but front-end cleanliness — not by `-Ztrust-verify`, which is
        // `off` on every ordinary build. A gate a flag can switch off is a lint;
        // this is a compilation-correctness check. See
        // `rustc_mir_transform::trust_once_reentrancy`.
        rustc_mir_transform::trust_check_once_initializer_reentrancy(tcx);
        // Trust (D2 tier 1): mint the ADAPTER_YIELD premises for local closures
        // handed to a core iterator adapter. It borrows each parent's
        // `mir_drops_elaborated_and_const_checked` (pre-inlining MIR), so it runs
        // BEFORE the backing-certificate initializer below, which can force
        // `optimized_mir` — and with it this pass's consumer — for some bodies. A
        // closure verified before this seam sees no premise and fails closed.
        // Self-gates on verification being enabled and on
        // `-Ztrust-no-adapter-yield`. See `trust_verify/adapter_yield.rs`.
        rustc_mir_transform::trust_init_adapter_yield_premises(tcx);
        // Trust (STR_BYTE_POSITION): certify the local `|b| b == K` closures from
        // their pre-inlining MIR, at the same pre-steal point. Self-gates on
        // verification and `-Ztrust-no-str-byte-position`. See
        // `trust_verify/byte_eq_predicate.rs`.
        rustc_mir_transform::trust_init_byte_eq_predicates(tcx);
        // Trust (2026-10-18, FRESH-CAPTURE-1): certify, from each parent's
        // pre-inlining MIR at the same pre-steal point, the by-reference captures of
        // a local closure that hold a fresh shared borrow in every value of its type.
        // Self-gates on verification. See `trust_verify/fresh_capture.rs`.
        rustc_mir_transform::trust_init_fresh_capture_premises(tcx);
        // Trust: compute interprocedural backing-invariant certificates now, while
        // post-analysis MIR (`mir_drops_elaborated_and_const_checked`) is still
        // borrowable — `optimized_mir` STEALS it later during codegen, and running
        // this inside that pass would cause a query cycle. Self-gates on whether
        // Trust verification is enabled. See docs/backing-cert-compiler-wiring.md.
        // Trust (#42): the companion refusal of an unconsumed `#[trust::<name>]`
        // does NOT live here. It runs in `rustc_resolve::macros`, at the one seam
        // every tool attribute passes through exactly once — see the E5
        // conservation check in `smart_resolve_macro_path`. A HIR walk at this
        // seam was tried and is strictly worse: lowering ALIASES one attribute
        // slice onto several HIR ids, so it double-reports, and it cannot see an
        // attribute that expansion already consumed.
        //
        // Trust (plan step 3.5, design §5.7): both initializers below are the verifier's
        // (each returns at once with verification off), so a Clean-origin body they build
        // (the backing inventory reads a Clean def's `optimized_mir`, measured on t1) is
        // charged to the reach counter's `verification` lane, not to `unattributed`.
        let clean_origin_reach = rustc_mir_transform::clean_origin_ir::clean_origin_reach::within(
            rustc_mir_transform::clean_origin_ir::clean_origin_reach::ReachLane::Verification,
        );
        rustc_mir_transform::trust_init_backing_certificates(tcx);
        // Trust #540 (R1): retain the pre-steal initialization seam, but the
        // strengthening authority is hard-disabled. The initializer therefore
        // stores an empty attribution map and every per-body flip remains a
        // fail-closed no-op until a non-forgeable authority lane is implemented.
        rustc_mir_transform::trust_init_r1_attributions(tcx);
        drop(clean_origin_reach);

        // A metadata-only binary has no codegen demand for HIR-less Clean
        // functions. Check the definitions actually referenced by Rust MIR
        // here, after the pre-steal initializers, independently of IR output or
        // verification flags. Unreferenced minted definitions stay undemanded.
        rustc_mir_transform::clean_origin_references::ensure_referenced(tcx);
    }

    // Trust (scope-truncation fix): make the verification universe ordering-
    // independent. Eagerly demand `optimized_mir` — and thus the TrustVerify pass —
    // for EVERY local function/closure NOW: after the pre-steal trust init hooks
    // above (they must read `mir_drops_elaborated_and_const_checked` before
    // `optimized_mir` steals it), and BEFORE the `has_errors_excluding_lint_errors`
    // gate below or `start_codegen`'s `has_errors_or_delayed_bugs` gate can
    // `raise_fatal` and cut off codegen collection. A per-function verification
    // error can therefore never prevent another function from being verified —
    // coverage no longer depends on which function happened to error first.
    // SOUNDNESS: a strict widening of coverage under an already-failing build; every
    // emitted error still fails the build at the gates below (fail-closed
    // preserved). Self-gates on trust verification being enabled and on this crate
    // being under verification.
    if front_end_errors_before_trust_hooks.is_none() {
        // Trust (plan step 3.5): a Clean-origin body this walk builds is the verifier's read.
        let _clean_origin_reach = rustc_mir_transform::clean_origin_ir::clean_origin_reach::within(
            rustc_mir_transform::clean_origin_ir::clean_origin_reach::ReachLane::Verification,
        );
        rustc_mir_transform::trust_ensure_whole_crate_verification(tcx);
        // Trust (spawn census P4): the census's trust-ir lane in shadow, after every verdict
        // was read and before the error gate. A no-op unless `-Ztrust-spawn-census-shadow`.
        rustc_mir_transform::trust_spawn_census_shadow(tcx);
    }
    // Trust (2026-09-29): upstream demands every coroutine's `optimized_mir` in the
    // eager layout check of `run_required_analyses`, so optimization-time diagnostics
    // (e.g. `#[rustc_force_inline]` refusals inside an `async` body) are reported even
    // for a crate with front-end errors. With verification enabled that layout is read
    // pre-steal and no longer optimizes the coroutine, so demand it here instead —
    // fixed order, at top level, never inside type computation, and before the error
    // gate below, like upstream. A cache hit for every coroutine the walk above
    // already verified. Self-gates on verification being enabled.
    rustc_mir_transform::trust_ensure_coroutine_optimized_mir(tcx);

    let sess = tcx.sess;

    // Avoid overwhelming user with errors if borrow checking failed.
    // I'm not sure how helpful this is, to be honest, but it avoids a
    // lot of annoying errors in the ui tests (basically,
    // lint warnings and so on -- kindck used to do this abort, but
    // kindck is gone now). -nmatsakis
    //
    // But we exclude lint errors from this, because lint errors are typically
    // less serious and we're more likely to want to continue (#87337).
    // Trust (CORE3): pending calculus reports cannot withhold original policy
    // failures when an independent error reaches this unchanged fatal gate.
    rustc_mir_transform::trust_finalize_calculus_reporting_on_error(tcx);
    if let Some(guar) = sess.dcx().has_errors_excluding_lint_errors() {
        guar.raise_fatal();
    }

    // Trust (typeck-moonshot P1, Phase 0): commit the per-crate witness store.
    // All body owners are typeck'd by `run_required_analyses` above, so every
    // mintable root is recorded by now. The stricter `has_errors_or_delayed_bugs`
    // gate (vs the lint-excluding gate above) guarantees no `ErrorGuaranteed`-
    // tainted crate is ever serialized. Pure side-effect (writes files, reads
    // finalized state); inert unless the witness lane mints, so
    // every other lane is byte-identical to upstream.
    if tcx.trust_witness_mint_active() && tcx.sess.dcx().has_errors_or_delayed_bugs().is_none() {
        rustc_mir_build::trust_witness_crate_finalize(tcx);
    }
    // Trust (P1 follow-on): reclaim any un-taken replay check-THIR (the single-
    // build lookaside). Normally drained-by-use in `thir_body`; a leftover only
    // occurs if a root was accepted but its `thir_body` was never demanded, and
    // is freed at gcx-drop regardless. Unconditional + cheap (empty off replay).
    let reclaimed = tcx.trust_witness_drain_thir_lookaside();
    if reclaimed > 0 {
        tracing::debug!(reclaimed, "trust-witness: reclaimed un-taken replay check-THIR");
    }

    // Trust: assemble the per-body THIR→trust-ir lowerings (collected at the
    // `mir_built` hook, the only pre-steal THIR seam) into one crate-level
    // `trust_ir::Module`. This runs for the differential lane (`-Ztrust-ir-lower`)
    // and for the first-class artifact lane (`--emit=trust-ir`). A requested
    // artifact is publication-grade: tripwires or write failures are fatal.
    //
    // Body coverage: `run_required_analyses` forces the hook for every body owner —
    // via `mir_borrowck` on ordinary lanes, and via the explicit `mir_built` force on
    // the deferred-verification lane (see the Step-3 gate there; the explicit force is
    // required because `check_unsafety` early-returns for `#[custom_mir]` bodies before
    // its own `mir_built` call).
    //
    // Error gate: the gate above confirmed no check that RAN emitted an error. On the
    // deferred lane that is a weaker statement than on other lanes — deferred checks
    // emit nothing because they never run — which is exactly why the module carries an
    // in-band, digest-bearing DISCLOSURE (crate_module.rs; deliberately not a routable
    // obligation — see docs/PROOF_CARRYING_LANE.md §2.1) and why the note below is
    // emitted. No artifact is ever emitted for a crate that failed a check that ran.
    // Trust (2026-09-16): the Clean-origin CALL gate belongs to the LANGUAGE, not
    // to the trust-ir artifact lane. `clean_origin_mir` refuses a `def` whose body
    // reads a `static` or calls an impure Rust fn with "cannot be called from
    // Rust", it is kernel-backed, and it is deliberately NOT behind
    // `-Ztrust-verify=off` (docs/design/2026-08-04-two-language-compiler-architecture.md,
    // ruling v7/D1). But it runs inside the `optimized_mir` PROVIDER for the
    // Clean-origin def, and nothing demanded that MIR on an ordinary lane: a
    // binary compiled with `--emit metadata` never monomorphizes it,
    // `run_required_analyses` does not walk it, and
    // `trust_ensure_whole_crate_verification` returns early under
    // `-Ztrust-verify=off`. The only demand was the one BELOW, inside the
    // `-Ztrust-ir-lower` block — so an artifact-lane flag decided whether a
    // language gate ran at all.
    //
    // MEASURED on `tests/ui/trust/clean_origin_static_read_refused.rs`, whose
    // `applyRead` reads a `static mut` and returns 7 and then 19 for the same
    // argument: its `plain_on`/`optimized_on` revisions refused it while
    // `plain_off`/`optimized_off` compiled it, the two differing only in
    // `-Ztrust-ir-lower`. Three fixtures carried that hole as annotated,
    // deliberately-red `_off` revisions.
    //
    // This demand is keyed on HIR NAMES rather than on the producer's emitted
    // edges (`hir_named_clean_origin_defs` explains the trade), because the
    // producer's registry is filled by a `mir_built` hook that is itself gated on
    // `-Ztrust-ir-lower`. It is free on every crate without a `clean { … }`
    // island, and it runs AFTER the front-end error gate above, so it cannot fire
    // on a crate that did not type-check.
    //
    // Trust (plan step 3.5, docs/design/2026-10-02-step3-lean-through-trust-ir.md §5.1): NOT on F1
    // with the trust-ir producer running. There the Clean recorder runs on every compile,
    // verification on or off, and demands no `clean_origin_mir` body; the call gate's two rules
    // (purity, the cross-language cycle) are decided on trust-ir after the finalize below
    // (`check_rust_callees_on_f1`). Each demand here is charged to the reach counter's `recorder`
    // lane (design §1.2 lists these demands beside the recorder's own).
    let clean_records_on_f1 = rustc_mir_transform::clean_origin_ir::records_on_f1(tcx);
    if !clean_records_on_f1 {
        for def in rustc_mir_transform::clean_origin_ir::hir_named_clean_origin_defs(tcx) {
            let _ask = rustc_mir_transform::clean_origin_ir::clean_origin_reach::ask(
                tcx.sess,
                rustc_mir_transform::clean_origin_ir::clean_origin_reach::ReachLane::Recorder,
            );
            let _ = tcx.optimized_mir(def.to_def_id());
        }
    }

    if tcx.sess.trust_ir_lower_enabled()
        || tcx.sess.opts.output_types.contains_key(&OutputType::TrustIr)
    {
        // Trust: HIR-less Clean callees are absent from run_required_analyses' body
        // walk. Demand the real native gate for emitted call/address references
        // before IR assembly can mask its refusal with an unsigned declaration
        // error. This analysis seam is outside every mir_built provider, and the
        // registry borrow has ended before optimized_mir can re-enter lowering.
        // Unused minted defs remain undemanded on verification-off lanes; this
        // does not collect Clean-origin IR or change its recorded:false policy.
        // Trust (plan step 3.5): not on F1, for the reason given at the HIR-named demand above.
        if !clean_records_on_f1 {
            for def in rustc_mir_build::trust_ir_referenced_clean_origin_defs(tcx) {
                let _ask = rustc_mir_transform::clean_origin_ir::clean_origin_reach::ask(
                    tcx.sess,
                    rustc_mir_transform::clean_origin_ir::clean_origin_reach::ReachLane::Recorder,
                );
                let _ = tcx.optimized_mir(def.to_def_id());
            }
        }
        // Trust (deferred-verification lane): tell the user, every time, in-band with
        // their build output. The artifact records the deferral for machines; this
        // records it for humans. Deliberately not a lint (cannot be `allow`ed away) and
        // deliberately unconditional on the lane.
        if tcx.trust_defer_verification() {
            tcx.dcx().note(
                "trust-ir artifact lane: borrow/ownership checking was NOT PERFORMED for \
                 ordinary fn bodies. This compile does not reject borrow-invalid code, \
                 and no in-tree verifier can currently decide borrow safety from the \
                 emitted module (it carries no loan/region facts, and bodies the \
                 producer could not lower have no representation at all). The module \
                 records this as a digest-bearing DISCLOSURE and must not be treated as \
                 borrow-checked.",
            );
        }
        // Trust (IR-1, docs/design/2026-08-27-two-language-direct-to-trust-ir.md
        // §3): collect the Clean-origin trust-ir spellings — under verification,
        // where the eager body demand is deliberate fail-closed tightening; and
        // (plan step 3.5, docs/design/2026-10-02-step3-lean-through-trust-ir.md
        // §5.1) on EVERY F1 compile, verification on or off, demanding no
        // `clean_origin_mir` body. Verification-off artifact lanes that are not F1
        // make no demand and the coverage sidecar records the absence instead. This
        // crate performs the hand-off because rustc_mir_build (the finalizer's
        // home) cannot depend on rustc_mir_transform (the collection's home).
        let trust_clean_origin_ir = rustc_mir_transform::clean_origin_ir::recorder_lane(tcx)
            .map(|lane| rustc_mir_transform::clean_origin_ir::collect_clean_origin_ir(tcx, lane));
        rustc_mir_build::trust_ir_crate_finalize(tcx, trust_clean_origin_ir);
        // Trust (plan step 3.5, design §5.1): on F1 the Clean language's Rust-callee rules
        // (purity on the conserved trust-ir effect census, the cross-language cycle on the
        // module's call graph) are decided here, on the module the finalize just assembled and
        // the effect-conservation check just judged. A refusal is fatal, as on the MIR lane.
        if clean_records_on_f1 {
            rustc_mir_transform::clean_origin_ir::check_rust_callees_on_f1(tcx);
        }
    }

    // Trust (CORE3): the source module is actually final, or was not published.
    // Close only withheld Trust reports; no optimization or producer is rerun.
    rustc_mir_transform::trust_finalize_calculus_reporting(tcx);

    // Trust (lane CTFE, `-Ztrust-ctfe-trivial-probe`, default OFF): MEASUREMENT
    // ONLY. Here, and not at the seam, because for a trivial const there IS no
    // seam: `mir_built` fast-paths it, so `mir_for_ctfe` — and with it
    // `try_flip_ctfe` — is never demanded. Every `mir_built` in the crate has
    // executed by now (borrow-checking forced it, and `is_trivial_const` forces
    // it for the rest), so the flip registry is fully populated and no trivial
    // const's built body has been stolen. AFTER `trust_ir_crate_finalize`, so
    // that the probe's registry `take`s cannot perturb the published coverage
    // artifact even in principle — the control arm then has nothing left to
    // catch. The probe installs no body and changes no emitted code.
    rustc_mir_transform::trust_probe_trivial_const_flips(tcx);

    // Trust (deferred-verification lane, Step 4): the `misc_checking_3` sweep is
    // DIAGNOSTIC-ONLY — effective visibilities, private-in-public, deathness,
    // clashing extern decls, privacy, lint expectations, diagnostic items. Nothing
    // the trust-ir producer reads depends on any of their RESULTS (the producer ran
    // at `mir_built`, long before this point, and the artifact was finalized just
    // above). On the artifact lane they are deferred with the rest of the
    // rejection-only work; every other lane runs them unchanged.
    //
    // Note the ordering: `trust_ir_crate_finalize` above already wrote the module,
    // so skipping this sweep cannot change the artifact — only which diagnostics a
    // human sees, which is precisely what the lane's disclosure records.
    let trust_skip_diagnostic_sweeps = tcx.trust_defer_verification();
    if !trust_skip_diagnostic_sweeps {
        sess.time("misc_checking_3", || {
            par_fns(&mut [
                &mut || {
                    tcx.ensure_ok().effective_visibilities(());

                    par_fns(&mut [
                        &mut || {
                            tcx.par_hir_for_each_module(|module| {
                                tcx.ensure_ok().check_private_in_public(module)
                            })
                        },
                        &mut || {
                            tcx.par_hir_for_each_module(|module| {
                                tcx.ensure_ok().check_mod_deathness(module)
                            });
                        },
                        &mut || {
                            // Trust: the `--emit=trust-ir`-only lane is an ARTIFACT lane —
                            // late lints are diagnostics for a human check/build flow, and
                            // skipping them is the rustdoc precedent (~2.4% of lane time).
                            // Any other primary output (metadata or link; dep-info is a
                            // side artifact) keeps the upstream-identical lint pass.
                            let trust_ir_only = tcx.sess.opts.output_types.trust_ir_only();
                            if !trust_ir_only {
                                sess.time("lint_checking", || {
                                    rustc_lint::check_crate(tcx);
                                });
                            }
                        },
                        &mut || {
                            tcx.ensure_ok().clashing_extern_declarations(());
                        },
                    ]);
                },
                &mut || {
                    sess.time("privacy_checking_modules", || {
                        tcx.par_hir_for_each_module(|module| {
                            tcx.ensure_ok().check_mod_privacy(module);
                        });
                    });
                },
            ]);

            // This check has to be run after all lints are done processing. We don't
            // define a lint filter, as all lint checks should have finished at this point.
            sess.time("check_lint_expectations", || tcx.ensure_ok().check_expectations(None));

            // This query is only invoked normally if a diagnostic is emitted that needs any
            // diagnostic item. If the crate compiles without checking any diagnostic items,
            // we will fail to emit overlap diagnostics. Thus we invoke it here unconditionally.
            let _ = tcx.all_diagnostic_items(());

            // This query is only invoked normally if a diagnostic is emitted that needs any
            // canonical symbol. If the crate compiles without checking any runtime symbols,
            // we will fail to emit overlap diagnostics. Thus we invoke it here unconditionally.
            let _ = tcx.all_canonical_symbols(());
        });
    } // Trust (Step 4): end of the deferred diagnostic-only sweep.

    // If `-Zvalidate-mir` is set, we also want to compute the final MIR for each item
    // (either its `mir_for_ctfe` or `optimized_mir`) since that helps uncover any bugs
    // in MIR optimizations that may only be reachable through codegen, or other codepaths
    // that requires the optimized/ctfe MIR, coroutine bodies, or evaluating consts.
    // Nevertheless, wait after type checking is finished, as optimizing code that does not
    // type-check is very prone to ICEs.
    if tcx.sess.opts.unstable_opts.validate_mir {
        sess.time("ensuring_final_MIR_is_computable", || {
            tcx.par_hir_body_owners(|def_id| {
                if !tcx.is_trivial_const(def_id) {
                    tcx.instance_mir(ty::InstanceKind::Item(def_id.into()));
                }
            });
        });
    }
    crate::trust_body_census::complete(tcx);
    rustc_mir_transform::trust_lean_census::complete(tcx);
}

/// Runs the codegen backend, after which the AST and analysis can
/// be discarded.
pub(crate) fn start_codegen<'tcx>(
    codegen_backend: &dyn CodegenBackend,
    tcx: TyCtxt<'tcx>,
) -> (Box<dyn Any>, CrateInfo, EncodedMetadata) {
    tcx.sess.timings.start_section(tcx.sess.dcx(), TimingSection::Codegen);

    // Hook for tests.
    if let Some((def_id, _)) = tcx.entry_fn(())
        && find_attr!(tcx, def_id, RustcDelayedBugFromInsideQuery)
    {
        tcx.ensure_ok().trigger_delayed_bug(def_id);
    }

    // Don't run this test assertions when not doing codegen. Compiletest tries to build
    // build-fail tests in check mode first and expects it to not give an error in that case.
    if tcx.sess.opts.output_types.should_codegen() {
        rustc_symbol_mangling::test::dump_symbol_names_and_def_paths(tcx);
    }

    // Don't do code generation if there were any errors. Likewise if
    // there were any delayed bugs, because codegen will likely cause
    // more ICEs, obscuring the original problem.
    if let Some(guar) = tcx.sess.dcx().has_errors_or_delayed_bugs() {
        guar.raise_fatal();
    }

    info!("Pre-codegen\n{:?}", tcx.debug_stats());

    // Trust: on the `--emit=trust-ir`-only lane the rmeta is pure waste — no
    // metadata output is requested, codegen and linking are skipped
    // (`should_codegen`/`should_link` are false), and the artifact was already
    // written at the analysis seam. Measured 2.1-2.7% of lane time encoding a
    // 4.18MB rmeta that was then discarded. Any other output combination keeps
    // the upstream-identical path.
    let output_types = &tcx.sess.opts.output_types;
    let metadata = if output_types.contains_key(&OutputType::TrustIr)
        && !output_types.contains_key(&OutputType::Metadata)
        && !output_types.should_codegen()
        && !output_types.should_link()
    {
        rustc_metadata::EncodedMetadata::empty()
    } else {
        // Trust (plan step 3.5, design §5.7): a Clean-origin body the encoder builds is the
        // cross-crate reader's (I7, until increment 6), counted as such.
        let _clean_origin_reach = rustc_mir_transform::clean_origin_ir::clean_origin_reach::within(
            rustc_mir_transform::clean_origin_ir::clean_origin_reach::ReachLane::CrossCrate,
        );
        match rustc_metadata::fs::encode_and_write_metadata(tcx) {
            Ok(metadata) => metadata,
            Err(guar) => guar.raise_fatal(),
        }
    };

    let is_host_metadata = tcx
        .sess
        .opts
        .unstable_opts
        .offload
        .iter()
        .any(|o| matches!(o, rustc_session::config::Offload::HostMetadata(_)));

    let codegen = tcx.sess.time("codegen_crate", || {
        if tcx.sess.opts.unstable_opts.no_codegen
            || !tcx.sess.opts.output_types.should_codegen()
            || is_host_metadata
        {
            tcx.sess.dcx().abort_if_errors();

            if is_host_metadata {
                rustc_monomorphize::write_host_metadata_offload_manifest(tcx);
            }

            // Linker::link will skip join_codegen in case of a `CompiledModules` Any value.
            Box::new(CompiledModules { modules: vec![], allocator_module: None })
        } else {
            codegen_backend.codegen_crate(tcx)
        }
    });

    info!("Post-codegen\n{:?}", tcx.debug_stats());
    rustc_monomorphize::trust_instance_census::complete(tcx);
    // Trust (wall A, instance-flip probe — MEASUREMENT ONLY): after `codegen_crate`
    // the mono partition is computed and every flip decision has fired; report, per
    // stashed generic `agreed` body, the concrete instances codegen actually
    // demanded. No-op unless `-Ztrust-instance-flip-probe` is set.
    rustc_mir_build::trust_instance_probe_finalize(tcx);
    // Trust (wall A, the INSTANCE flip seam): the production census — one row per recorded
    // generic body with its offered/flipped/refused instance counts, measured by the seam itself.
    // No-op unless the instance lane is enabled.
    rustc_mir_transform::trust_instance_flip_census(tcx);

    // This must run after monomorphization so that all generic types
    // have been instantiated.
    if tcx.sess.opts.unstable_opts.print_type_sizes {
        tcx.sess.code_stats.print_type_sizes();
    }

    let crate_info = CrateInfo::new(tcx, codegen_backend.target_cpu(tcx.sess));

    (codegen, crate_info, metadata)
}

/// Compute and validate the crate name.
pub fn get_crate_name(sess: &Session, krate_attrs: &[ast::Attribute]) -> Symbol {
    // We validate *all* occurrences of `#![crate_name]`, pick the first find and
    // if a crate name was passed on the command line via `--crate-name` we enforce
    // that they match.
    // We perform the validation step here instead of later to ensure it gets run
    // in all code paths that require the crate name very early on, namely before
    // macro expansion.

    let attr_crate_name =
        parse_crate_name(sess, krate_attrs, ShouldEmit::EarlyFatal { also_emit_lints: true });

    let validate = |name, span| {
        rustc_session::output::validate_crate_name(sess, name, span);
        name
    };

    if let Some(crate_name) = &sess.opts.crate_name {
        let crate_name = Symbol::intern(crate_name);
        if let Some((attr_crate_name, span)) = attr_crate_name
            && attr_crate_name != crate_name
        {
            sess.dcx().emit_err(diagnostics::CrateNameDoesNotMatch {
                span,
                crate_name,
                attr_crate_name,
            });
        }
        return validate(crate_name, None);
    }

    if let Some((crate_name, span)) = attr_crate_name {
        return validate(crate_name, Some(span));
    }

    if let Input::File(ref path) = sess.io.input
        && let Some(file_stem) = path.file_stem().and_then(|s| s.to_str())
    {
        if file_stem.starts_with('-') {
            sess.dcx().emit_err(diagnostics::CrateNameInvalid { crate_name: file_stem });
        } else {
            return validate(Symbol::intern(&file_stem.replace('-', "_")), None);
        }
    }

    sym::rust_out
}

pub(crate) fn parse_crate_name(
    sess: &Session,
    attrs: &[ast::Attribute],
    emit_errors: ShouldEmit,
) -> Option<(Symbol, Span)> {
    if !attrs.iter().any(|attr| attr.has_name(sym::crate_name)) {
        return None;
    }
    let Attribute::Parsed(AttributeKind::CrateName { name, name_span, .. }) =
        AttributeParser::parse_limited_sym_should_emit(
            sess,
            attrs,
            &[sym::crate_name],
            DUMMY_SP,
            None,
            emit_errors,
        )?
    else {
        unreachable!("crate_name is the only attr we could've parsed here");
    };

    Some((name, name_span))
}

/// Trust (WS7.10 / F-114): `unsupported_crate_type_is_fatal` is the backend's
/// `CodegenBackend::unsupported_crate_type_is_fatal` answer for this session.
/// When it is `true`, a requested crate type the backend does not advertise is
/// an ERROR (every refused type is named, then compilation aborts) instead of
/// the upstream "dropping unsupported crate type" warning, which let a plain
/// `rustc main.rs` under trust-cg exit 0 having produced nothing. Target-level
/// drops (`invalid_output_for_target`) are unchanged.
pub fn collect_crate_types(
    session: &Session,
    backend_crate_types: &[CrateType],
    codegen_backend_name: &'static str,
    unsupported_crate_type_is_fatal: bool,
    attrs: &[ast::Attribute],
    crate_span: Span,
) -> Vec<CrateType> {
    // If we're generating a test executable, then ignore all other output
    // styles at all other locations
    if session.opts.test {
        if !session.target.executables {
            session.dcx().emit_warn(diagnostics::UnsupportedCrateTypeForTarget {
                crate_type: CrateType::Executable,
                target_triple: &session.opts.target_triple,
            });
            return Vec::new();
        }
        return vec![CrateType::Executable];
    }

    // Shadow `sdylib` crate type in interface build.
    if session.opts.unstable_opts.build_sdylib_interface {
        return vec![CrateType::Rlib];
    }

    // Only check command line flags if present. If no types are specified by
    // command line, then reuse the empty `base` Vec to hold the types that
    // will be found in crate attributes.
    // JUSTIFICATION: before wrapper fn is available
    #[allow(rustc::bad_opt_access)]
    let mut base = session.opts.crate_types.clone();
    if base.is_empty() {
        if attrs.iter().any(|attr| attr.has_name(sym::crate_type))
            && let Some(Attribute::Parsed(AttributeKind::CrateType(crate_type))) =
                AttributeParser::parse_limited_sym_should_emit(
                    session,
                    attrs,
                    &[sym::crate_type],
                    crate_span,
                    None,
                    ShouldEmit::EarlyFatal { also_emit_lints: false },
                )
        {
            base.extend(crate_type);
        }

        if base.is_empty() {
            base.push(default_output_for_target(session));
        } else {
            base.sort();
            base.dedup();
        }
    }

    let mut refused_by_backend = false;
    base.retain(|crate_type| {
        if invalid_output_for_target(session, *crate_type) {
            session.dcx().emit_warn(diagnostics::UnsupportedCrateTypeForTarget {
                crate_type: *crate_type,
                target_triple: &session.opts.target_triple,
            });
            false
        } else if !backend_crate_types.contains(crate_type) {
            if unsupported_crate_type_is_fatal {
                refused_by_backend = true;
                session.dcx().emit_err(diagnostics::UnsupportedCrateTypeForCodegenBackendFatal {
                    crate_type: *crate_type,
                    codegen_backend: codegen_backend_name,
                    supported: supported_crate_type_list(backend_crate_types),
                });
            } else {
                session.dcx().emit_warn(diagnostics::UnsupportedCrateTypeForCodegenBackend {
                    crate_type: *crate_type,
                    codegen_backend: codegen_backend_name,
                });
            }
            false
        } else {
            true
        }
    });

    // Trust (WS7.10): abort before any supported type is compiled, so a mixed
    // request such as `--crate-type=bin,rlib` does not leave a partial rlib
    // behind a failing exit status.
    if refused_by_backend {
        session.dcx().abort_if_errors();
    }

    base
}

fn supported_crate_type_list(backend_crate_types: &[CrateType]) -> String {
    if backend_crate_types.is_empty() {
        return "(none)".to_owned();
    }
    backend_crate_types
        .iter()
        .map(|crate_type| format!("`{crate_type}`"))
        .collect::<Vec<_>>()
        .join(", ")
}

/// Returns default crate type for target
///
/// Default crate type is used when crate type isn't provided neither
/// through cmd line arguments nor through crate attributes
///
/// It is CrateType::Executable for all platforms but iOS as there is no
/// way to run iOS binaries anyway without jailbreaking and
/// interaction with Rust code through static library is the only
/// option for now
fn default_output_for_target(sess: &Session) -> CrateType {
    if !sess.target.executables { CrateType::StaticLib } else { CrateType::Executable }
}

// Trust: the query-provider admission cases are Trust's and read the private
// provider table, so they stay in this module's own tree.
#[cfg(test)]
mod tests;
