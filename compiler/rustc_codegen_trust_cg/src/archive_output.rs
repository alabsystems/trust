//! Preserve the exact already-gated Compiler object through rlib construction.
//!
//! The handoff is private live state, never a report/digest read from disk. The
//! standard archive builder writes into an owned sibling staging directory. Its
//! stored member is checked BEFORE renaming to the final output, stdout/artifact
//! notifications or cleanup. Failed checks preserve an existing final output.
//! This adds no function grade and proves nothing about other native libraries,
//! symbol-index/linker behavior or a loaded executable.

use std::fs::{self, File};
use std::io::{self, Read};
use std::path::{Path, PathBuf};
use std::sync::Arc;

use rustc_codegen_ssa::back::archive::{
    AddArchiveKind, ArArchiveBuilderBuilder, ArchiveBuilder, ArchiveBuilderBuilder,
    ArchiveEntryKind, ArchiveSymbols,
};
use rustc_codegen_ssa::{CompiledModules, ModuleKind};
use rustc_fs_util::TempDirBuilder;
use rustc_session::Session;
use trust_cg_bridge::archive_object::{ArchiveObjectPadding, bind_archive_object};

const MAX_ARCHIVE_BYTES: u64 = 512 * 1024 * 1024;

/// Owned bytes moved directly from the gated Compiler unit at join_codegen.
/// They outlive ordinary temporary-file cleanup without rereading a mutable
/// object file or constructing authority from a serializable certificate.
#[derive(Debug)]
pub(super) struct CompilerArchiveObject {
    name: String,
    path: PathBuf,
    member_name: String,
    bytes: Vec<u8>,
}
impl CompilerArchiveObject {
    pub(super) fn new(name: String, path: PathBuf, bytes: Vec<u8>) -> Result<Self, String> {
        let member_name = path
            .file_name()
            .and_then(|n| n.to_str())
            .ok_or("Compiler archive object filename is not UTF-8")?
            .to_owned();
        if bytes.is_empty() {
            return Err("Compiler archive object is empty".into());
        }
        Ok(Self { name, path, member_name, bytes })
    }

    pub(super) fn require_modules(&self, compiled: &CompiledModules) -> Result<(), String> {
        let [module] = compiled.modules.as_slice() else {
            return Err("Compiler archive handoff requires its exact one codegen unit".into());
        };
        if module.name != self.name
            || module.object.as_deref() != Some(self.path.as_path())
            || module.kind != ModuleKind::Regular
            || compiled.allocator_module.is_some()
            || module.global_asm_object.is_some()
            || module.dwarf_object.is_some()
        {
            return Err("Compiler archive handoff differs from the actual compiled modules".into());
        }
        Ok(())
    }
}

pub(super) struct CheckedArchiveBuilderBuilder {
    pub(super) expected: Arc<CompilerArchiveObject>,
}
impl ArchiveBuilderBuilder for CheckedArchiveBuilderBuilder {
    fn new_archive_builder<'a>(&self, sess: &'a Session) -> Box<dyn ArchiveBuilder + 'a> {
        Box::new(CheckedArchiveBuilder {
            sess,
            inner: ArArchiveBuilderBuilder.new_archive_builder(sess),
            expected: Arc::clone(&self.expected),
        })
    }
}
struct CheckedArchiveBuilder<'a> {
    sess: &'a Session,
    inner: Box<dyn ArchiveBuilder + 'a>,
    expected: Arc<CompilerArchiveObject>,
}
impl ArchiveBuilder for CheckedArchiveBuilder<'_> {
    fn add_file(&mut self, path: &Path, kind: ArchiveEntryKind) {
        self.inner.add_file(path, kind);
    }
    fn add_archive(&mut self, path: &Path, kind: AddArchiveKind<'_>) -> io::Result<()> {
        self.inner.add_archive(path, kind)
    }
    fn build(self: Box<Self>, output: &Path, symbols: Option<ArchiveSymbols>) -> bool {
        let Self { sess, inner, expected } = *self;
        let padding = if sess.target.archive_format == "darwin" {
            ArchiveObjectPadding::DarwinEightByte
        } else {
            ArchiveObjectPadding::Exact
        };
        let (built, binding) = publish_bound_archive(output, &expected, padding, |staged| {
            inner.build(staged, symbols)
        })
        .unwrap_or_else(|reason| {
            sess.dcx()
                .fatal(format!("trust-cg Compiler archive object preservation failed: {reason}"))
        });
        sess.dcx().note(format!(
            "trust-cg Compiler archive object preserved: archive sha256 {}, member `{}`, \
             object sha256 {}, {} object bytes + {} archive padding bytes; \
             other members/linking/loaded-image proofs remain separate",
            binding.archive_sha256,
            binding.member_name,
            binding.object_sha256,
            binding.object_bytes,
            binding.padding_bytes,
        ));
        built
    }
}

/// The same transaction is exercised with the real pinned writer in focused
/// tests. The closure never receives the final path. Its result is published
/// only after complete actual member verification.
fn publish_bound_archive(
    output: &Path,
    expected: &CompilerArchiveObject,
    padding: ArchiveObjectPadding,
    build: impl FnOnce(&Path) -> bool,
) -> Result<(bool, trust_cg_bridge::archive_object::ArchiveObjectBinding), String> {
    // Common-driver cleanup removes the CGU path after linking. Publishing an
    // archive onto that same file would let cleanup delete a successful result.
    // As in standalone object publication, aliases are an explicit refusal.
    if output == expected.path {
        return Err("archive output aliases its temporary Compiler object".into());
    }
    match fs::metadata(output) {
        Ok(final_metadata) => {
            let source_metadata = fs::metadata(&expected.path)
                .map_err(|e| format!("identify Compiler input object: {e}"))?;
            if super::output_artifacts::same_file_identity(&source_metadata, &final_metadata)? {
                return Err("archive output aliases its temporary Compiler object".into());
            }
        }
        Err(e) if e.kind() == io::ErrorKind::NotFound => {}
        Err(e) => return Err(format!("identify archive destination: {e}")),
    }
    let parent =
        output.parent().filter(|p| !p.as_os_str().is_empty()).unwrap_or_else(|| Path::new("."));
    let staging = TempDirBuilder::new()
        .prefix("trust-checked-archive-")
        .tempdir_in(parent)
        .map_err(|e| format!("create private archive staging: {e}"))?;
    let name = output.file_name().ok_or("archive output has no filename")?;
    let staged = staging.path().join(name);
    let built = build(&staged);
    let binding = read_and_bind(&staged, expected, padding)?;
    fs::rename(&staged, output).map_err(|e| format!("publish verified archive: {e}"))?;
    Ok((built, binding))
}

fn read_and_bind(
    output: &Path,
    expected: &CompilerArchiveObject,
    padding: ArchiveObjectPadding,
) -> Result<trust_cg_bridge::archive_object::ArchiveObjectBinding, String> {
    let mut archive = Vec::new();
    File::open(output)
        .map_err(|e| format!("open actual archive: {e}"))?
        .take(MAX_ARCHIVE_BYTES + 1)
        .read_to_end(&mut archive)
        .map_err(|e| format!("read actual archive: {e}"))?;
    let bound = bind_archive_object(&archive, &expected.member_name, &expected.bytes, padding)?;
    Ok(bound.binding().clone())
}

#[cfg(test)]
mod tests;
