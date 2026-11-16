//! Exact object membership in a stored archive, not linking or proof admission.
//!
//! The expected object must come from an independently selected current input.
//! A retained digest or an archive member cannot authenticate itself. Darwin's
//! pinned writer includes up to seven newline bytes in the MEMBER size; those
//! are checked against the known original length, never trimmed heuristically.

use object::read::archive::{ArchiveFile, ArchiveKind};
use serde::Serialize;

use crate::compiled_object::{CompiledObject, ObjectFormat};
use crate::object_replay::artifact_digest;

const MAX_ARCHIVE_BYTES: usize = 512 * 1024 * 1024;
const MAX_OBJECT_BYTES: usize = 256 * 1024 * 1024;
const MAX_MEMBERS: usize = 65_536;
const MAX_NAME_BYTES: usize = 64 * 1024;

/// Chosen from the actual target archive format, not inferred by discarding
/// bytes until an untrusted hash happens to match.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
pub enum ArchiveObjectPadding {
    Exact,
    DarwinEightByte,
}

/// Comparison data only. This covers ONE selected member; other archive
/// members, symbol-index/linker behavior and a loaded image remain outside it.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct ArchiveObjectBinding {
    pub archive_sha256: String,
    pub archive_bytes: usize,
    pub member_name: String,
    pub member_data_offset: u64,
    pub member_bytes: usize,
    pub member_sha256: String,
    pub object_bytes: usize,
    pub object_sha256: String,
    pub padding: ArchiveObjectPadding,
    pub padding_bytes: usize,
    pub ordinary_members: usize,
}

/// Borrowed actual archive bytes after full byte comparison with the current
/// expected object. Construction and deserialization cannot grant a grade.
#[derive(Debug)]
pub struct BoundArchiveObject<'a> {
    object: &'a [u8],
    binding: ArchiveObjectBinding,
}
impl<'a> BoundArchiveObject<'a> {
    pub fn object(&self) -> &'a [u8] {
        self.object
    }
    pub fn binding(&self) -> &ArchiveObjectBinding {
        &self.binding
    }
}

/// Parse the complete stored archive and require exactly one literal named
/// member. Thin/external members, duplicates and malformed later members are
/// refused. All object bytes, including non-text sections and symbol tables,
/// must match; only the target's exact bounded archive padding is separate.
pub fn bind_archive_object<'a>(
    archive: &'a [u8],
    member_name: &str,
    expected_object: &[u8],
    padding: ArchiveObjectPadding,
) -> Result<BoundArchiveObject<'a>, String> {
    if archive.is_empty()
        || archive.len() > MAX_ARCHIVE_BYTES
        || expected_object.is_empty()
        || expected_object.len() > MAX_OBJECT_BYTES
        || member_name.is_empty()
        || member_name.len() > MAX_NAME_BYTES
        || member_name.as_bytes().contains(&0)
    {
        return Err("archive object binding input budget/name".into());
    }
    let file = ArchiveFile::parse(archive).map_err(|e| format!("archive header: {e}"))?;
    if file.is_thin() {
        return Err(
            "archive object binding requires stored members, not thin external paths".into()
        );
    }
    if !matches!(
        file.kind(),
        ArchiveKind::Unknown
            | ArchiveKind::Gnu
            | ArchiveKind::Gnu64
            | ArchiveKind::Bsd
            | ArchiveKind::Bsd64
            | ArchiveKind::Coff
    ) || archive.len() % 2 != 0
    {
        return Err("unsupported or truncated common archive envelope".into());
    }
    let extra = match padding {
        ArchiveObjectPadding::Exact => 0,
        ArchiveObjectPadding::DarwinEightByte => {
            if !matches!(file.kind(), ArchiveKind::Bsd | ArchiveKind::Bsd64) {
                return Err("Darwin object padding requires an actual BSD/Darwin archive".into());
            }
            let object = CompiledObject::parse(expected_object).map_err(|e| e.to_string())?;
            if object.format != ObjectFormat::MachO {
                return Err("Darwin object padding requires the current Mach-O object".into());
            }
            (8 - expected_object.len() % 8) % 8
        }
    };
    let expected_member_len =
        expected_object.len().checked_add(extra).ok_or("archive object padding length overflow")?;
    let mut selected = None;
    let mut count = 0usize;
    for member in file.members() {
        let member = member.map_err(|e| format!("archive member: {e}"))?;
        count = count
            .checked_add(1)
            .filter(|n| *n <= MAX_MEMBERS)
            .ok_or("archive member population budget")?;
        if member.is_thin() || member.name().len() > MAX_NAME_BYTES {
            return Err("archive member storage/name budget".into());
        }
        // Read every range before success, even an unrelated later member.
        let data = member.data(archive).map_err(|e| format!("archive member data: {e}"))?;
        let end = member
            .file_range()
            .0
            .checked_add(data.len() as u64)
            .and_then(|end| usize::try_from(end).ok())
            .ok_or("archive member end overflow")?;
        // object::ArchiveMember advances over this external byte without
        // checking it. Validate presence/value before accepting the envelope.
        if end % 2 != 0 && archive.get(end) != Some(&b'\n') {
            return Err("archive member external alignment padding is missing or invalid".into());
        }
        if member.name() != member_name.as_bytes() {
            continue;
        }
        if selected.is_some() {
            return Err("archive contains duplicate selected object members".into());
        }
        if data.len() != expected_member_len
            || data.get(..expected_object.len()) != Some(expected_object)
            || !data[expected_object.len()..].iter().all(|byte| *byte == b'\n')
        {
            return Err(
                "archive member differs from the current whole object or exact padding".into()
            );
        }
        selected = Some((member.file_range().0, data));
    }
    let (offset, data) = selected.ok_or("archive lacks the selected current object member")?;
    let object = &data[..expected_object.len()];
    Ok(BoundArchiveObject {
        object,
        binding: ArchiveObjectBinding {
            archive_sha256: artifact_digest(archive),
            archive_bytes: archive.len(),
            member_name: member_name.into(),
            member_data_offset: offset,
            member_bytes: data.len(),
            member_sha256: artifact_digest(data),
            object_bytes: object.len(),
            object_sha256: artifact_digest(object),
            padding,
            padding_bytes: extra,
            ordinary_members: count,
        },
    })
}

#[cfg(test)]
mod tests;
