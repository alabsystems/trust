//! Trust (DC-18a): the `-Ztrust-path-free` refusal.
//!
//! A unit is shared between checkouts only when the compiler can show that its metadata
//! names no host path; nothing is shared on trust. Under the option, a compile that
//! writes crate metadata ends with one error, and leaves no rlib or rmeta (temporaries
//! kept by `-Csave-temps` included), when that metadata would carry an absolute host path.
//! The checks run in order and the compile stops at the first that refuses:
//!
//! 1. Environment reads, before anything is encoded or reused (`fs.rs`): each
//!    `env!`/`option_env!` value holding a host path, recorded during expansion
//!    (`rustc_builtin_macros::env`, with its span), and each other tracked read in
//!    `Session::env_depinfo` (a proc macro's `proc_macro::tracked::env_var`, the
//!    compiler's own). Expansion runs in every session, so a reused rmeta cannot hide one.
//!    A host path in an environment value is refused even when nothing writes it into the
//!    metadata (`include_str!(concat!(env!("CARGO_MANIFEST_DIR"), ..))`): the value is
//!    checkout-specific input, and nothing shows where it went.
//! 2. While encoding (`encoder.rs`): every local source file's name, exactly as metadata
//!    writes it, whether or not a span in this metadata names it (a Trust-IR entry writes
//!    the names of files no span reaches), and every file a proc-macro crate re-exports
//!    (`imported-source-file`); and every native library's name (`-l`, `#[link]`).
//! 3. After encoding, only when nothing above refused: the bytes of the metadata written
//!    (reused or not) are searched for this session's host prefixes
//!    (`Session::trust_path_free_prefixes`). This judges values, not where they came from:
//!    a constant or static copied from a dependency compiled without the option, a string
//!    a proc macro made from an untracked read, an attribute, a valtree.
//!
//! Without the option nothing here runs and nothing is recorded.

use std::path::Path;

use rustc_crate_store::NativeLib;
use rustc_data_structures::fx::FxHashSet;
use rustc_middle::ty::TyCtxt;
use rustc_session::Session;
use rustc_span::trust_path_free::{RecordPath, Refusal, host_path_in_value, record};
use rustc_span::{ErrorGuaranteed, FileName, SourceFile, Span};

use crate::diagnostics::{FailedCreateEncodedMetadata, TrustPathFree};

/// Whether a path exists on this host: the file-name rule's test of a rewritten root.
fn on_host(path: &Path) -> bool {
    std::fs::symlink_metadata(path).is_ok()
}

fn push(sess: &Session, refusal: Refusal) {
    sess.trust_path_free_refusals.borrow_mut().push(refusal);
}

/// Step 1: refuses the unit when an environment read held a host path.
pub(crate) fn refuse_before_encoding(sess: &Session) -> Option<ErrorGuaranteed> {
    if !sess.opts.unstable_opts.trust_path_free {
        return None;
    }
    let refused: FxHashSet<String> = sess
        .trust_path_free_refusals
        .borrow()
        .iter()
        .flat_map(|refusal| refusal.fields.iter())
        .filter(|(key, _)| *key == "var")
        .map(|(_, var)| var.clone())
        .collect();
    let tracked: Vec<_> = sess.env_depinfo.borrow().iter().copied().collect();
    for (var, value) in tracked {
        let Some(value) = value else { continue };
        if refused.contains(var.as_str()) {
            continue;
        }
        if let Some(path) = host_path_in_value(value.as_str(), sess.trust_path_free_prefixes()) {
            push(
                sess,
                Refusal {
                    origin: "env",
                    describe: format!(
                        "the tracked environment read of `{}`",
                        var.as_str().escape_debug()
                    ),
                    path: RecordPath::from_bytes(path.as_bytes()),
                    fields: vec![("var", var.to_string()), ("read", "tracked".to_string())],
                    span: None,
                },
            );
        }
    }
    emit(sess)
}

/// Step 2: judges one source file, `exported` being its name as metadata writes it.
pub(crate) fn judge_file_name(tcx: TyCtxt<'_>, file: &SourceFile, exported: &FileName) {
    let Some((origin, path)) = file.name.trust_unrewritten_host_path(exported, &on_host) else {
        return;
    };
    let mut fields = vec![("file", file.name.prefer_local_unconditionally().to_string())];
    let (origin, describe) = if file.is_imported() {
        let krate = tcx.crate_name(file.cnum);
        fields.push(("crate", krate.to_string()));
        (
            "imported-source-file",
            format!("{} of a file imported from crate `{krate}`", origin.describe()),
        )
    } else {
        (origin.as_str(), origin.describe().to_string())
    };
    push(
        tcx.sess,
        Refusal {
            origin,
            describe,
            path: RecordPath::from_path(&path),
            fields,
            span: Some(Span::with_root_ctxt(file.start_pos, file.start_pos)),
        },
    );
}

/// Step 2: judges one native library's name (an `-l` value, a `#[link(name)]`).
pub(crate) fn judge_native_library(tcx: TyCtxt<'_>, lib: &NativeLib) {
    let Some(path) = host_path_in_value(lib.name.as_str(), tcx.sess.trust_path_free_prefixes())
    else {
        return;
    };
    push(
        tcx.sess,
        Refusal {
            origin: "native-library",
            describe: format!("the native library `{}`", lib.name.as_str().escape_debug()),
            path: RecordPath::from_bytes(path.as_bytes()),
            fields: vec![("kind", format!("{:?}", lib.kind))],
            span: lib.foreign_module.map(|module| tcx.def_span(module)),
        },
    );
}

/// Step 3, after encoding: reports the encoder's refusals, or, when it had none, searches
/// the written `outputs` for host prefixes.
pub(crate) fn refuse_after_encoding(sess: &Session, outputs: &[&Path]) -> Option<ErrorGuaranteed> {
    if !sess.opts.unstable_opts.trust_path_free {
        return None;
    }
    if sess.trust_path_free_refusals.borrow().is_empty() && sess.dcx().has_errors().is_none() {
        let prefixes = sess.trust_path_free_prefixes();
        for output in outputs {
            let bytes = std::fs::read(output)
                .unwrap_or_else(|err| sess.dcx().emit_fatal(FailedCreateEncodedMetadata { err }));
            let name = output.file_name().map_or_else(
                || output.display().to_string(),
                |name| name.to_string_lossy().into_owned(),
            );
            for found in prefixes.occurrences(&bytes) {
                let prefix = String::from_utf8_lossy(&found.prefix).into_owned();
                push(
                    sess,
                    Refusal {
                        origin: "metadata",
                        describe: format!(
                            "a value written into the metadata (`{name}` byte {}, under the \
                             host directory `{prefix}`)",
                            found.offset
                        ),
                        path: RecordPath::from_bytes(&found.path),
                        fields: vec![
                            ("output", name.clone()),
                            ("prefix", prefix),
                            ("offset", found.offset.to_string()),
                        ],
                        span: None,
                    },
                );
            }
        }
    }
    emit(sess)
}

/// Removes what a refused compile encoded, `-Csave-temps` or not: the metadata files and
/// the temporary directory that holds them.
pub(crate) fn remove_outputs(files: &[&Path], dir: &Path) {
    for file in files {
        let _ = std::fs::remove_file(file);
    }
    let _ = std::fs::remove_dir_all(dir);
}

/// Emits the one error, naming the first refusal and counting the others.
fn emit(sess: &Session) -> Option<ErrorGuaranteed> {
    let refusals = sess.trust_path_free_refusals.borrow();
    let first = refusals.first()?;
    let fields: Vec<(&str, &str)> =
        first.fields.iter().map(|(key, value)| (*key, value.as_str())).collect();
    Some(sess.dcx().emit_err(TrustPathFree {
        span: first.span,
        path: first.path.text.clone(),
        origin: first.describe.clone(),
        record: record(first.origin, &fields, &first.path, refusals.len() - 1),
    }))
}
