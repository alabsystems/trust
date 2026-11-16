//! Verify an oversized packed base blob without buffering its body.
//!
//! The index is a bounded locator in the original sealed view. Git object
//! identity is checked over the inflated bytes. This does not authenticate
//! the rest of the pack or implement streaming delta resolution.

use super::{MAX_OBJECTS, MAX_TOTAL_BYTES, custody::OwnedView};
use crate::util::CargoResult;
use anyhow::{Context as _, ensure};
use flate2::{CrcReader, Decompress, FlushDecompress, Status};
use gix::odb::pack::{data, index};
use std::ffi::{OsStr, OsString};
use std::fs::File;
use std::io::{self, BufRead as _, BufReader, Read as _, Seek as _, SeekFrom, Write};
use std::path::{Path, PathBuf};

const PACK_HEADER_LEN: u64 = 12;
const SHA1_LEN: usize = 20;
const MIN_V2_INDEX_LEN: usize = 8 + 256 * 4 + 2 * SHA1_LEN;
// One SHA-1, CRC, offset and possible 64-bit overflow offset per entry.
const MAX_INDEX_LEN: u64 = (MIN_V2_INDEX_LEN + MAX_OBJECTS * (SHA1_LEN + 4 + 4 + 8)) as u64;
const BUFFER_LEN: usize = 32 * 1024;

/// Bound extra index scans and pack input across the whole transaction,
/// including repeated scans and entry bytes that do not yield blob output.
pub(super) struct ReadBudget(u64);

impl Default for ReadBudget {
    fn default() -> Self {
        Self(MAX_TOTAL_BYTES)
    }
}

impl ReadBudget {
    fn reserve(&mut self, len: u64) -> CargoResult<()> {
        self.0 = self
            .0
            .checked_sub(len)
            .context("oversized packed Git blob read budget exceeded")?;
        Ok(())
    }
}

struct IndexedBlob {
    pack_name: OsString,
    count: u32,
    pack_checksum: gix::hash::ObjectId,
    offset: u64,
    successor: Option<u64>,
    last_offset: u64,
    crc: u32,
}

impl IndexedBlob {
    fn find(
        name: &OsStr,
        mut file: impl io::Read,
        len: u64,
        oid: &gix::hash::oid,
        budget: &mut ReadBudget,
    ) -> CargoResult<Option<Self>> {
        ensure!(
            ((MIN_V2_INDEX_LEN as u64)..=MAX_INDEX_LEN).contains(&len),
            "packed Git index outside supported size"
        );
        budget.reserve(len)?;
        let mut bytes = vec![0; usize::try_from(len)?];
        file.read_exact(&mut bytes)?;
        let index = index::File::from_data(&bytes[..], PathBuf::from(name), gix::hash::Kind::Sha1)?;
        ensure!(
            index.version() == index::Version::V2 && index.num_objects() as usize <= MAX_OBJECTS,
            "oversized packed Git blob requires a bounded version 2 SHA-1 index"
        );
        // Layout and monotone fanout alone do not prove that a lookup saw
        // every matching OID. Check the actual bounded table, including rows
        // outside the lookup's bucket.
        let mut matches = (0..index.num_objects()).filter(|&row| index.oid_at_index(row) == oid);
        let entry = matches.next();
        ensure!(
            matches.next().is_none(),
            "packed Git index repeats the oversized blob object ID"
        );
        ensure!(
            index.lookup(oid) == entry,
            "packed Git index lookup disagrees with the object ID table"
        );
        let Some(entry) = entry else {
            return Ok(None);
        };
        let mut hash = gix::hash::hasher(gix::hash::Kind::Sha1);
        hash.update(&bytes[..bytes.len() - SHA1_LEN]);
        ensure!(
            hash.try_finalize()? == index.index_checksum(),
            "packed Git index checksum mismatch"
        );
        let offset = index.pack_offset_at_index(entry);
        let mut successor = None;
        let mut last_offset = 0;
        for row in 0..index.num_objects() {
            let other = index.pack_offset_at_index(row);
            ensure!(
                other >= PACK_HEADER_LEN && (other != offset || row == entry),
                "invalid packed Git index offset"
            );
            last_offset = last_offset.max(other);
            if other > offset && successor.is_none_or(|next| other < next) {
                successor = Some(other);
            }
        }
        Ok(Some(Self {
            pack_name: Path::new(name).with_extension("pack").into_os_string(),
            count: index.num_objects(),
            pack_checksum: index.pack_checksum(),
            offset,
            successor,
            last_offset,
            crc: index
                .crc32_at_index(entry)
                .context("missing pack entry CRC")?,
        }))
    }

    fn stream(
        &self,
        pack: &mut File,
        len: u64,
        oid: &gix::hash::oid,
        size: u64,
        budget: &mut ReadBudget,
        output: &mut dyn Write,
    ) -> CargoResult<()> {
        let pack_end = len
            .checked_sub(SHA1_LEN as u64)
            .context("truncated Git pack")?;
        ensure!(
            self.last_offset < pack_end,
            "packed Git index offset outside pack"
        );
        let span = self.successor.unwrap_or(pack_end) - self.offset;
        budget.reserve(span + PACK_HEADER_LEN + SHA1_LEN as u64)?;
        let mut header = [0; PACK_HEADER_LEN as usize];
        pack.read_exact(&mut header)?;
        let (_, count) = data::header::decode(&header)?;
        ensure!(
            count == self.count,
            "Git pack and index object counts disagree"
        );
        pack.seek(SeekFrom::Start(pack_end))?;
        let mut trailer = [0; SHA1_LEN];
        pack.read_exact(&mut trailer)?;
        ensure!(
            self.pack_checksum.as_slice() == trailer.as_slice(),
            "Git pack trailer disagrees with index"
        );
        pack.seek(SeekFrom::Start(self.offset))?;
        stream_entry(pack, span, self.offset, self.crc, oid, size, output)
    }
}

fn stream_entry(
    source: impl io::Read,
    span: u64,
    offset: u64,
    crc: u32,
    oid: &gix::hash::oid,
    size: u64,
    output: &mut dyn Write,
) -> CargoResult<()> {
    let mut input = CrcReader::new(BufReader::with_capacity(BUFFER_LEN, source.take(span)));
    let entry = data::Entry::from_read(&mut input, offset, SHA1_LEN)?;
    ensure!(
        entry.header == data::entry::Header::Blob,
        "oversized Git object requires a packed base blob"
    );
    ensure!(
        entry.decompressed_size == size,
        "packed Git blob header size disagrees"
    );
    let compressed_len = span
        .checked_sub(entry.data_offset - offset)
        .context("packed Git blob header exceeds indexed span")?;
    let mut hash = gix::hash::hasher(gix::hash::Kind::Sha1);
    hash.update(&gix::objs::encode::loose_header(
        gix::objs::Kind::Blob,
        size,
    ));
    let mut inflater = Decompress::new(true);
    let mut decoded = [0; BUFFER_LEN];
    loop {
        let input_before = inflater.total_in();
        let output_before = inflater.total_out();
        let status = inflater.decompress(input.fill_buf()?, &mut decoded, FlushDecompress::None)?;
        let used = (inflater.total_in() - input_before) as usize;
        let produced = (inflater.total_out() - output_before) as usize;
        input.consume(used);
        ensure!(
            inflater.total_out() <= size,
            "packed Git blob exceeds declared size"
        );
        hash.update(&decoded[..produced]);
        output.write_all(&decoded[..produced])?;
        if status == Status::StreamEnd {
            break;
        }
        ensure!(
            used != 0 || produced != 0,
            "truncated packed Git blob stream"
        );
    }
    ensure!(
        inflater.total_in() == compressed_len && inflater.total_out() == size,
        "packed Git blob does not match indexed span or declared size"
    );
    ensure!(input.crc().sum() == crc, "packed Git blob CRC mismatch");
    ensure!(
        hash.try_finalize()?.as_slice() == oid.as_bytes(),
        "corrupt locked Git blob: {oid}"
    );
    Ok(())
}

pub(super) fn verify(
    view: &OwnedView,
    sink: Option<&git2::Odb<'_>>,
    oid: git2::Oid,
    size: usize,
    budget: &mut ReadBudget,
) -> CargoResult<()> {
    ensure!(
        oid.as_bytes().len() == SHA1_LEN,
        "oversized packed Git blob requires a SHA-1 object ID"
    );
    let expected = gix::hash::oid::try_from_bytes(oid.as_bytes())?;
    let mut location = None;
    view.for_each_pack_index(|name, file, len| {
        if let Some(indexed) = IndexedBlob::find(name, file, len, expected, budget)? {
            ensure!(
                location.is_none(),
                "oversized Git blob has multiple pack entries: {oid}"
            );
            location = Some(indexed);
        }
        Ok(())
    })?;
    let location = location
        .with_context(|| format!("oversized Git object requires a packed base blob: {oid}"))?;
    // Only the native default loose writer of the newly created staged
    // repository is supplied here. Preflight creates no output ODB.
    let mut writer = sink
        .map(|odb| odb.writer(size, git2::ObjectType::Blob))
        .transpose()?;
    let mut discard = io::sink();
    let output: &mut dyn Write = match &mut writer {
        Some(writer) => writer,
        None => &mut discard,
    };
    view.read_pack(&location.pack_name, |file, len| {
        location.stream(file, len, expected, size as u64, budget, output)
    })?;
    if let Some(mut writer) = writer {
        ensure!(
            writer.finalize()? == oid,
            "Git source object write disagrees: {oid}"
        );
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use flate2::{Compression, write::ZlibEncoder};

    fn encoded_entry(header: data::entry::Header, declared: u64, body: &[u8]) -> Vec<u8> {
        let mut bytes = Vec::new();
        header.write_to(declared, &mut bytes).unwrap();
        let mut compressed = ZlibEncoder::new(bytes, Compression::fast());
        compressed.write_all(body).unwrap();
        compressed.finish().unwrap()
    }

    fn blob_id(body: &[u8]) -> gix::hash::ObjectId {
        gix::objs::compute_hash(gix::hash::Kind::Sha1, gix::objs::Kind::Blob, body).unwrap()
    }

    fn crc(bytes: &[u8]) -> u32 {
        let mut crc = flate2::Crc::new();
        crc.update(bytes);
        crc.sum()
    }

    fn verify_entry(
        bytes: &[u8],
        crc: u32,
        expected: &gix::hash::oid,
        size: u64,
    ) -> CargoResult<()> {
        stream_entry(
            bytes,
            bytes.len() as u64,
            PACK_HEADER_LEN,
            crc,
            expected,
            size,
            &mut io::sink(),
        )
    }

    #[test]
    fn valid_zlib_and_crc_do_not_substitute_for_git_identity() {
        let body = b"exact locked blob";
        let size = body.len() as u64;
        let raw = encoded_entry(data::entry::Header::Blob, size, body);
        verify_entry(&raw, crc(&raw), blob_id(body).as_ref(), size).unwrap();
        let wrong = verify_entry(
            &raw,
            crc(&raw),
            blob_id(b"wrong locked blob").as_ref(),
            size,
        )
        .unwrap_err();
        assert!(wrong.to_string().contains("corrupt locked Git blob"));
        let bad_crc = verify_entry(&raw, crc(&raw) ^ 1, blob_id(body).as_ref(), size).unwrap_err();
        assert!(bad_crc.to_string().contains("CRC mismatch"));
    }

    #[test]
    fn exact_zlib_end_span_and_output_size_are_required() {
        let body = [0xb5; 2 * BUFFER_LEN + 1];
        let size = body.len() as u64;
        let expected = blob_id(&body);
        let raw = encoded_entry(data::entry::Header::Blob, size, &body);
        verify_entry(&raw, crc(&raw), expected.as_ref(), size).unwrap();
        // Cut the zlib trailer after producing the full declared body.
        let truncated = &raw[..raw.len() - 1];
        assert!(
            verify_entry(truncated, crc(truncated), expected.as_ref(), size)
                .unwrap_err()
                .to_string()
                .contains("truncated")
        );
        let mut extended = raw;
        extended.push(0);
        assert!(
            verify_entry(&extended, crc(&extended), expected.as_ref(), size)
                .unwrap_err()
                .to_string()
                .contains("indexed span")
        );
        let oversized = encoded_entry(data::entry::Header::Blob, size - 1, &body);
        assert!(
            verify_entry(&oversized, crc(&oversized), expected.as_ref(), size - 1)
                .unwrap_err()
                .to_string()
                .contains("exceeds declared size")
        );
    }

    #[test]
    fn delta_entries_do_not_enter_the_base_stream() {
        let body = b"delta program";
        let size = body.len() as u64;
        let expected = blob_id(body);
        let raw = encoded_entry(
            data::entry::Header::RefDelta { base_id: expected },
            size,
            body,
        );
        assert!(
            verify_entry(&raw, crc(&raw), expected.as_ref(), size)
                .unwrap_err()
                .to_string()
                .contains("requires a packed base blob")
        );
    }

    fn index_fixture(oid: &gix::hash::oid, bucket: u8, offsets: &[(u32, u64)]) -> Vec<u8> {
        let mut raw = vec![0xff, b't', b'O', b'c'];
        raw.extend(2u32.to_be_bytes());
        for row in 0..=u8::MAX {
            let count = if row >= bucket {
                offsets.len() as u32
            } else {
                0
            };
            raw.extend(count.to_be_bytes());
        }
        for _ in offsets {
            raw.extend(oid.as_bytes());
        }
        for _ in offsets {
            raw.extend(0u32.to_be_bytes()); // fixture entry CRC
        }
        for &(slot, _) in offsets {
            raw.extend((0x8000_0000 | slot).to_be_bytes());
        }
        for &(_, offset) in offsets {
            raw.extend(offset.to_be_bytes());
        }
        raw.extend([0; SHA1_LEN]); // fixture pack trailer
        let mut hash = gix::hash::hasher(gix::hash::Kind::Sha1);
        hash.update(&raw);
        raw.extend(hash.try_finalize().unwrap().as_slice());
        raw
    }

    #[test]
    fn index_uses_the_full_validated_64_bit_offset_and_charges_each_read() {
        let id = blob_id(b"indexed body");
        let oid: &gix::hash::oid = id.as_ref();
        let bytes = index_fixture(oid, oid.first_byte(), &[(0, 2_821_653_954)]);
        let mut budget = ReadBudget(bytes.len() as u64);
        let read = |bytes: &[u8], budget: &mut ReadBudget| {
            IndexedBlob::find(
                OsStr::new("test.idx"),
                bytes,
                bytes.len() as u64,
                id.as_ref(),
                budget,
            )
        };
        let found = read(&bytes, &mut budget).unwrap().unwrap();
        assert_eq!(found.offset, 2_821_653_954);
        assert!(
            read(&bytes, &mut budget)
                .err()
                .unwrap()
                .to_string()
                .contains("read budget exceeded")
        );
        let invalid_slot = index_fixture(oid, oid.first_byte(), &[(1, 2_821_653_954)]);
        assert!(read(&invalid_slot, &mut ReadBudget::default()).is_err());
        let mut corrupt_checksum = bytes;
        *corrupt_checksum.last_mut().unwrap() ^= 1;
        assert!(
            read(&corrupt_checksum, &mut ReadBudget::default())
                .err()
                .unwrap()
                .to_string()
                .contains("index checksum mismatch")
        );
    }

    #[test]
    fn repeated_and_fanout_hidden_target_rows_refuse() {
        let id = blob_id(b"indexed body");
        let oid: &gix::hash::oid = id.as_ref();
        let read = |bytes: &[u8]| {
            IndexedBlob::find(
                OsStr::new("test.idx"),
                bytes,
                bytes.len() as u64,
                oid,
                &mut ReadBudget::default(),
            )
            .err()
            .expect("inconsistent index must refuse")
            .to_string()
        };
        let repeated = index_fixture(oid, oid.first_byte(), &[(0, 12), (1, 24)]);
        assert!(read(&repeated).contains("repeats the oversized blob"));
        let hidden = index_fixture(oid, oid.first_byte() ^ 1, &[(0, 12)]);
        assert!(read(&hidden).contains("lookup disagrees"));
    }
}
