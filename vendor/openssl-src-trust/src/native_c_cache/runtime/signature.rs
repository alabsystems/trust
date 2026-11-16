//! Verify Apple's content-derived cache UUID, not a copied UUID field.
//!
//! Apple's cache_builder/SubCache.cpp derives UUID from SHA256(CodeDirectory)
//! before inserting UUID and re-signing page0. Reconstruct that exact value
//! after checking every data page. Mapping selection has the native UUID's
//! 122-bit strength; complete file bytes are independently hashed with SHA256.

use sha2::{Digest, Sha256};
use std::fs::File;
use std::io::{Read, Seek, SeekFrom};

const MAX_SIGNATURE: u64 = 32 * 1024 * 1024;

pub(super) struct Verified {
    pub digest: [u8; 32],
    pub header: Vec<u8>,
}

fn be32(bytes: &[u8], at: usize) -> Result<u32, String> {
    Ok(u32::from_be_bytes(
        bytes
            .get(at..at.checked_add(4).ok_or("signature offset overflow")?)
            .ok_or("truncated native CodeDirectory")?
            .try_into()
            .unwrap(),
    ))
}

fn le64(bytes: &[u8], at: usize) -> Result<u64, String> {
    Ok(u64::from_le_bytes(
        bytes
            .get(at..at.checked_add(8).ok_or("header offset overflow")?)
            .ok_or("truncated native cache header")?
            .try_into()
            .unwrap(),
    ))
}

pub(super) fn verify(file: &mut File, expected: [u8; 16]) -> Result<Verified, String> {
    let length = file.metadata().map_err(|e| e.to_string())?.len();
    let mut header = vec![0_u8; 400];
    file.seek(SeekFrom::Start(0)).map_err(|e| e.to_string())?;
    file.read_exact(&mut header).map_err(|e| e.to_string())?;
    if !header.starts_with(b"dyld_v1") || header[88..104] != expected {
        return Err("native cache header differs from its live/parent UUID".into());
    }
    let signature_offset = le64(&header, 40)?;
    let signature_size = le64(&header, 48)?;
    if signature_size == 0
        || signature_size > MAX_SIGNATURE
        || signature_offset.checked_add(signature_size) != Some(length)
    {
        return Err("unsupported native cache signature envelope".into());
    }
    let mut signature = vec![0_u8; signature_size as usize];
    file.seek(SeekFrom::Start(signature_offset))
        .map_err(|e| e.to_string())?;
    file.read_exact(&mut signature).map_err(|e| e.to_string())?;
    if be32(&signature, 0)? != 0xfade0cc0 {
        return Err("native cache has no embedded signature superblob".into());
    }
    let blob_length = be32(&signature, 4)? as usize;
    let count = be32(&signature, 8)? as usize;
    if blob_length > signature.len() || count == 0 || count > 16 || 12 + count * 8 > blob_length {
        return Err("invalid native cache signature index".into());
    }
    let mut directory = None;
    for index in 0..count {
        let at = 12 + index * 8;
        let kind = be32(&signature, at)?;
        if kind != 0 && !(0x1000..0x1006).contains(&kind) {
            continue;
        }
        let offset = be32(&signature, at + 4)? as usize;
        if offset < 12 + count * 8 || be32(&signature, offset)? != 0xfade0c02 {
            return Err("invalid native cache CodeDirectory index".into());
        }
        let size = be32(&signature, offset + 4)? as usize;
        let end = offset
            .checked_add(size)
            .ok_or("native CodeDirectory overflow")?;
        if size < 88 || end > blob_length {
            return Err("truncated native CodeDirectory".into());
        }
        if directory.replace(signature[offset..end].to_vec()).is_some() {
            return Err("ambiguous native cache CodeDirectory".into());
        }
    }
    let mut directory = directory.ok_or("native cache has no CodeDirectory")?;
    let version = be32(&directory, 8)?;
    let hash_offset = be32(&directory, 16)? as usize;
    let slots = be32(&directory, 28)? as usize;
    let code_limit = be32(&directory, 32)? as u64;
    let page_log = directory[39];
    if version != 0x20400
        || directory[36] != 32
        || directory[37] != 2
        || !(12..=16).contains(&page_log)
        || slots == 0
        || code_limit != signature_offset
        || le64(&directory, 56)? != 0
        || hash_offset < 88
        || hash_offset
            .checked_add(slots.checked_mul(32).ok_or("native page table overflow")?)
            .is_none_or(|end| end > directory.len())
    {
        return Err("unsupported native cache CodeDirectory recipe".into());
    }
    let page_size = 1_usize << page_log;
    if (slots as u64).checked_mul(page_size as u64) != Some(code_limit) {
        return Err("native cache page table does not cover its complete data".into());
    }
    file.seek(SeekFrom::Start(0)).map_err(|e| e.to_string())?;
    let mut digest = Sha256::new();
    let mut page = vec![0_u8; page_size];
    for index in 0..slots {
        file.read_exact(&mut page).map_err(|e| e.to_string())?;
        let actual = Sha256::digest(&page);
        let at = hash_offset + index * 32;
        if directory[at..at + 32] != actual[..] {
            return Err("native runtime data failed its CodeDirectory page hash".into());
        }
        digest.update(&page);
        if index == 0 {
            page[88..104].fill(0);
            directory[at..at + 32].copy_from_slice(&Sha256::digest(&page));
        }
    }
    let mut tail = vec![0_u8; signature_size as usize];
    file.read_exact(&mut tail).map_err(|e| e.to_string())?;
    if tail != signature {
        return Err("native cache signature changed during validation".into());
    }
    digest.update(&tail);
    let hash = Sha256::digest(&directory);
    let mut derived: [u8; 16] = hash[..16].try_into().unwrap();
    derived[6] = (derived[6] & 0x0f) | 0x30;
    derived[8] = (derived[8] & 0x3f) | 0x80;
    if derived != expected {
        return Err("native cache bytes do not derive the actual mapped UUID".into());
    }
    Ok(Verified {
        digest: digest.finalize().into(),
        header,
    })
}
