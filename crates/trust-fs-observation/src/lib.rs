// SPDX-License-Identifier: MIT OR Apache-2.0
// Copyright 2026 Andrew Yates

//! Shared bounded filesystem observations, without execution or proof authority.
//!
//! A serialized snapshot is data. Only a live observation/window retains change
//! stamps; decoding a snapshot cannot manufacture execution-window custody.

pub mod effective_access;
pub mod file_identity;
pub mod observation;
pub mod tool_lookup;

use serde::{Deserialize, Serialize};

/// Transient scanner work, including partial attempts that fail closed.
/// Metadata reads count symlink_metadata calls, excluding opens and fstat.
/// Bytes hashed count file data, excluding hash framing and link spelling.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct InputWork {
    pub entries: u64,
    pub input_bytes: u64,
    pub bytes_hashed: u64,
    pub metadata_reads: u64,
    pub resolution_steps: u64,
    pub link_reads: u64,
    pub observations: u64,
    pub revalidations: u64,
}

// Match the scanner's former cargo-util adapter exactly: incremental updates,
// lowercase hex and resetting finish. The implementation is Trust-owned SHA256.
struct Sha256(trust_sha2::Sha256);

impl Sha256 {
    fn new() -> Self {
        use trust_sha2::Digest as _;
        Self(trust_sha2::Sha256::new())
    }

    fn update(&mut self, bytes: &[u8]) -> &mut Self {
        use trust_sha2::Digest as _;
        self.0.update(bytes);
        self
    }

    fn finish_hex(&mut self) -> String {
        use trust_sha2::Digest as _;
        let hash = std::mem::replace(&mut self.0, trust_sha2::Sha256::new());
        format!("{:x}", hash.finalize())
    }
}

#[cfg(test)]
mod tests {
    use super::{InputWork, Sha256};

    #[test]
    fn digest_adapter_preserves_streaming_hex_and_reset() {
        let mut hash = Sha256::new();
        hash.update(b"a").update(b"bc");
        assert_eq!(
            hash.finish_hex(),
            "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
        );
        assert_eq!(
            hash.finish_hex(),
            "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
        );
    }

    #[test]
    fn work_telemetry_wire_fields_remain_exact() {
        let work = InputWork {
            entries: 1,
            input_bytes: 2,
            bytes_hashed: 3,
            metadata_reads: 4,
            resolution_steps: 5,
            link_reads: 6,
            observations: 7,
            revalidations: 8,
        };
        assert_eq!(
            serde_json::to_string(&work).unwrap(),
            "{\"entries\":1,\"input_bytes\":2,\"bytes_hashed\":3,\"metadata_reads\":4,\"resolution_steps\":5,\"link_reads\":6,\"observations\":7,\"revalidations\":8}"
        );
        assert!(serde_json::from_str::<InputWork>("{\"entries\":1}").is_err());
    }
}
