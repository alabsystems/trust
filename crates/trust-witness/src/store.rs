//! Witness store: a packed per-crate file `<StableCrateId>.twit` mapping the
//! sound witness key to the encoded per-root payload.
//!
//! Packing (vs one file per root) keeps warm reads to a single mmap-friendly
//! open — the P0 measurement had per-file reads at 15.5ms vs 0.4ms packed.

use std::collections::BTreeMap;
use std::path::Path;

/// Deterministic per-entry integrity digest (FNV-1a/64 over `key || payload`).
///
/// Graceful-degradation guard (SOUNDNESS_AUDIT rank 5): a witness minted by this
/// compiler is always structurally complete, so `node_type` never faults in normal
/// operation. But an *adversarially/disk-corrupted* payload whose length framing
/// still parses decodes into an INCOMPLETE `TypeckResults`, and the check-THIR build
/// then calls `node_type` on a missing node → rustc `bug!` emits an ICE diagnostic
/// *before* `catch_unwind` can retract it, so the root fails CLOSED (rc=1) instead of
/// missing transparently. This digest lets `unpack` detect payload/key corruption at
/// LOAD and drop just that entry (clean per-root MISS) before decode ever runs.
/// Must be deterministic across compiles (the store is written by one compile and
/// read by the next) — FNV-1a is; `std`'s `DefaultHasher` is not guaranteed to be.
fn entry_digest(key: &[u8], payload: &[u8]) -> u64 {
    let mut h: u64 = 0xcbf2_9ce4_8422_2325; // FNV offset basis
    for &b in key.iter().chain(payload.iter()) {
        h ^= b as u64;
        h = h.wrapping_mul(0x0000_0100_0000_01b3); // FNV prime
    }
    h
}

/// Serialize a keyed set of witnesses into the packed store format. Each entry
/// carries a trailing per-entry digest (see `entry_digest`).
pub fn pack(entries: &BTreeMap<String, Vec<u8>>) -> Option<Vec<u8>> {
    if entries.len() > u32::MAX as usize
        || entries
            .iter()
            .any(|(key, bytes)| key.len() > u16::MAX as usize || bytes.len() > u32::MAX as usize)
    {
        return None;
    }
    let mut out = Vec::new();
    out.extend(crate::schema::STORE_MAGIC);
    out.extend((entries.len() as u32).to_le_bytes());
    for (key, bytes) in entries {
        out.extend((key.len() as u16).to_le_bytes());
        out.extend(key.as_bytes());
        out.extend((bytes.len() as u32).to_le_bytes());
        out.extend(bytes);
        out.extend(entry_digest(key.as_bytes(), bytes).to_le_bytes());
    }
    Some(out)
}

/// Parse a packed store back into its keyed map. Returns `None` on any
/// structural error (a corrupt store is a clean whole-crate miss).
pub fn unpack(bytes: &[u8]) -> Option<BTreeMap<String, Vec<u8>>> {
    if bytes.len() < 12 || &bytes[..8] != crate::schema::STORE_MAGIC {
        return None;
    }
    let mut o = 8usize;
    let rd_u32 = |b: &[u8], o: &mut usize| -> Option<u32> {
        let v = u32::from_le_bytes(b.get(*o..*o + 4)?.try_into().ok()?);
        *o += 4;
        Some(v)
    };
    let rd_u16 = |b: &[u8], o: &mut usize| -> Option<u16> {
        let v = u16::from_le_bytes(b.get(*o..*o + 2)?.try_into().ok()?);
        *o += 2;
        Some(v)
    };
    let rd_u64 = |b: &[u8], o: &mut usize| -> Option<u64> {
        let v = u64::from_le_bytes(b.get(*o..*o + 8)?.try_into().ok()?);
        *o += 8;
        Some(v)
    };
    let n = rd_u32(bytes, &mut o)?;
    // Every entry needs at least u16 key length + u32 payload length + u64 digest.
    // Bound corrupt counts by the bytes available before entering the loop.
    if n as usize > bytes.len().saturating_sub(o) / 14 {
        return None;
    }
    let mut map = BTreeMap::new();
    for _ in 0..n {
        let kl = rd_u16(bytes, &mut o)? as usize;
        let key = std::str::from_utf8(bytes.get(o..o + kl)?).ok()?.to_string();
        o += kl;
        let bl = rd_u32(bytes, &mut o)? as usize;
        let payload = bytes.get(o..o + bl)?.to_vec();
        o += bl;
        let stored = rd_u64(bytes, &mut o)?;
        // Per-entry integrity: a key/payload byte corruption that survives the
        // length framing would decode into an incomplete `TypeckResults` and
        // fail-CLOSED at `node_type`. SKIP just this entry on a digest mismatch, so
        // it becomes a clean per-root MISS while sibling entries still replay.
        // (Framing corruption desyncs the cursor and is still caught as a
        // whole-store MISS by the bounds reads and the terminal `o == len` check.)
        if entry_digest(key.as_bytes(), &payload) != stored {
            continue;
        }
        if map.insert(key, payload).is_some() {
            return None;
        }
    }
    (o == bytes.len()).then_some(map)
}

/// Read the packed store for a crate stem from `dir`, if present.
pub fn read(dir: &Path, stem: &str) -> Option<BTreeMap<String, Vec<u8>>> {
    let path = dir.join(format!("{stem}.twit"));
    let bytes = std::fs::read(path).ok()?;
    unpack(&bytes)
}

/// Write the packed store for a crate stem into `dir`.
pub fn write(dir: &Path, stem: &str, entries: &BTreeMap<String, Vec<u8>>) -> std::io::Result<()> {
    std::fs::create_dir_all(dir)?;
    let bytes = pack(entries).ok_or_else(|| {
        std::io::Error::new(
            std::io::ErrorKind::InvalidData,
            "trust-witness store exceeds its on-disk length fields",
        )
    })?;
    std::fs::write(dir.join(format!("{stem}.twit")), bytes)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn sample() -> BTreeMap<String, Vec<u8>> {
        BTreeMap::from([
            ("k1".to_string(), vec![1u8, 2, 3, 4]),
            ("k2".to_string(), vec![9u8, 8, 7]),
        ])
    }

    #[test]
    fn round_trips() {
        let e = sample();
        assert_eq!(unpack(&pack(&e).unwrap()).unwrap(), e);
    }

    #[test]
    fn corrupt_payload_byte_drops_only_that_entry() {
        let e = sample();
        let mut bytes = pack(&e).unwrap();
        // Flip a byte inside k1's payload region: magic(8)+count(4)+klen(2)+"k1"(2)
        // +plen(4) = 20 → first payload byte of the first (BTree-sorted) entry.
        bytes[20] ^= 0xff;
        let got = unpack(&bytes).expect("sibling entry still parses");
        assert!(!got.contains_key("k1"), "corrupt entry must be a clean MISS");
        assert_eq!(got.get("k2"), Some(&vec![9u8, 8, 7]), "sibling entry survives");
    }

    #[test]
    fn corrupt_magic_is_whole_store_miss() {
        let mut bytes = pack(&sample()).unwrap();
        bytes[0] ^= 0xff;
        assert!(unpack(&bytes).is_none());
    }

    #[test]
    fn truncated_store_is_whole_store_miss() {
        let bytes = pack(&sample()).unwrap();
        assert!(unpack(&bytes[..bytes.len() - 3]).is_none());
    }
}
