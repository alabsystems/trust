//! Trust: final native-output publication using the pinned rustc protocol.
//!
//! This does not emit, re-emit, or certify code. Both native frontends must first
//! pass their existing safety/proven-output gates and write those exact bytes.
//! Ordinary output files retain rustc's copy/overwrite behavior; the create-only
//! diagnostic replay sidecar is a separate contract.

use std::fs;

use rustc_codegen_ssa::back::write::produce_final_output_artifacts;
use rustc_codegen_ssa::{CompiledModules, ModuleKind};
use rustc_middle::dep_graph::WorkProductMap;
use rustc_session::Session;
use rustc_session::config::{OutFileName, OutputFilenames, OutputType, OutputTypes};

/// MIR belongs to rustc's analysis lane even though `should_codegen` includes
/// it. Only these two supported outputs request the native machine pipeline.
pub(super) fn native_machine_output_requested(outputs: &OutputTypes) -> bool {
    outputs.contains_key(&OutputType::Exe) || outputs.contains_key(&OutputType::Object)
}

/// Rustc's shared publisher treats a zero-module object request like a
/// multi-CGU request and can return without creating an object. Refuse that
/// missing capability explicitly, and bind its recomputed input filename to
/// the object the backend actually recorded before allowing publication.
fn validate_requested_object(
    compiled: &CompiledModules,
    outputs: &OutputFilenames,
) -> Result<(), String> {
    if !outputs.outputs.contains_key(&OutputType::Object) {
        return Ok(());
    }
    let [module] = compiled.modules.as_slice() else {
        return Err(format!(
            "--emit=obj requires exactly one emitted regular codegen unit; found {}. \
             Empty/type-only or multiple-object publication is not implemented by trust-cg",
            compiled.modules.len()
        ));
    };
    if module.kind != ModuleKind::Regular {
        return Err(
            "--emit=obj requires a regular codegen unit, not an allocator/metadata module".into()
        );
    }
    let expected = outputs.temp_path_for_cgu(OutputType::Object, &module.name);
    let Some(recorded) = &module.object else {
        return Err(format!("codegen unit `{}` did not emit a requested object", module.name));
    };
    if recorded != &expected {
        return Err(format!(
            "codegen unit `{}` recorded object `{}` but rustc would publish `{}`",
            module.name,
            recorded.display(),
            expected.display()
        ));
    }
    let metadata = fs::symlink_metadata(recorded).map_err(|error| {
        format!("cannot inspect emitted object `{}`: {error}", recorded.display())
    })?;
    if !metadata.file_type().is_file() || metadata.len() == 0 {
        return Err(format!(
            "emitted object `{}` is not a nonempty regular file",
            recorded.display()
        ));
    }
    if let OutFileName::Real(final_path) = outputs.path(OutputType::Object) {
        // Explicit emit paths can equal or alias the CGU temporary. Rustc's
        // shared publisher would then copy a file onto itself and may delete
        // it as a temporary afterward. Do not claim an artifact in that case.
        // Distinct existing output files remain ordinary overwrite targets.
        let aliases = if final_path == *recorded {
            true
        } else {
            match fs::metadata(&final_path) {
                Ok(final_metadata) => {
                    let source_metadata = fs::metadata(recorded).map_err(|error| {
                        format!("cannot identify emitted object `{}`: {error}", recorded.display())
                    })?;
                    same_file_identity(&source_metadata, &final_metadata)?
                }
                Err(error) if error.kind() == std::io::ErrorKind::NotFound => false,
                Err(error) => {
                    return Err(format!(
                        "cannot identify requested final object `{}`: {error}",
                        final_path.display()
                    ));
                }
            }
        };
        if aliases {
            return Err(format!(
                "requested final object `{}` aliases temporary CGU object `{}`; \
                 choose a distinct final output path",
                final_path.display(),
                recorded.display()
            ));
        }
    }
    Ok(())
}

#[cfg(unix)]
pub(super) fn same_file_identity(
    left: &fs::Metadata,
    right: &fs::Metadata,
) -> Result<bool, String> {
    use std::os::unix::fs::MetadataExt;
    Ok(left.dev() == right.dev() && left.ino() == right.ino())
}

#[cfg(windows)]
pub(super) fn same_file_identity(
    left: &fs::Metadata,
    right: &fs::Metadata,
) -> Result<bool, String> {
    use std::os::windows::fs::MetadataExt;
    match (
        left.volume_serial_number(),
        left.file_index(),
        right.volume_serial_number(),
        right.file_index(),
    ) {
        (Some(lv), Some(li), Some(rv), Some(ri)) => Ok(lv == rv && li == ri),
        _ => Err("cannot establish Windows file identity for object publication".into()),
    }
}

#[cfg(not(any(unix, windows)))]
pub(super) fn same_file_identity(
    _left: &fs::Metadata,
    _right: &fs::Metadata,
) -> Result<bool, String> {
    Err("cannot establish file identity on this object-publication host".into())
}

/// Every join path ends here, including analysis-only and empty rlib builds.
/// Metadata and dep-info remain common-driver outputs. Object naming (`-o`,
/// `--out-dir`, explicit emit paths), stdout, temporary-file cleanup, and JSON
/// notifications remain rustc's own behavior, not a second implementation.
pub(super) fn finish_codegen(
    sess: &Session,
    compiled: CompiledModules,
    outputs: &OutputFilenames,
) -> (CompiledModules, WorkProductMap) {
    if let Err(reason) = validate_requested_object(&compiled, outputs) {
        sess.dcx().fatal(format!("trust-cg object publication failed: {reason}"));
    }
    produce_final_output_artifacts(sess, &compiled, outputs);
    sess.dcx().abort_if_errors();
    (compiled, WorkProductMap::default())
}

#[cfg(test)]
mod tests;
