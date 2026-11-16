// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates

//! Bounded candidate DATA for the SAME source carrier. Neither acceptance nor
//! these candidate digests establishes archive selection, Seed or completion.
use super::*;
use crate::{ContextReply, bootstrap_graph::fixed_context};

pub const MAX_ARCHIVE_CANDIDATES: usize = 16;

#[derive(Clone, PartialEq, Eq)]
pub struct ArchiveCandidate {
    pub relative: Vec<u8>,
    pub sha256: [u8; 32],
}

#[derive(Clone, PartialEq, Eq)]
pub struct SourceCapture {
    pub request: Request,
    pub candidates: Vec<ArchiveCandidate>,
}
impl SourceCapture {
    pub fn validate(&self) -> io::Result<()> {
        self.request.validate()?;
        let mut seen = BTreeSet::new();
        if self.candidates.is_empty() || self.candidates.len() > MAX_ARCHIVE_CANDIDATES {
            return Err(invalid());
        }
        for candidate in &self.candidates {
            if !super::super::configuration::relative(&candidate.relative)
                || !candidate
                    .relative
                    .starts_with(b"bootstrap/trust-stage0/dist/")
                || candidate.relative.split(|byte| *byte == b'/').count() != 5
                || !seen.insert(&candidate.relative)
            {
                return Err(invalid());
            }
        }
        Ok(())
    }
    pub fn encode(&self) -> io::Result<Vec<u8>> {
        self.validate()?;
        let mut e = Encoder::new(138);
        e.number(1);
        e.frame_bytes(&self.request.encode()?)?;
        e.number(self.candidates.len() as u64);
        for candidate in &self.candidates {
            e.bytes(&candidate.relative)?;
            e.0.extend(candidate.sha256);
        }
        e.finish()
    }
    pub fn decode(bytes: &[u8]) -> io::Result<Self> {
        let mut d = header(bytes, 138)?;
        if d.number()? != 1 {
            return Err(invalid());
        }
        let request = Request::decode(&d.frame_bytes()?)?;
        let count = usize::try_from(d.number()?).map_err(|_| invalid())?;
        if !(1..=MAX_ARCHIVE_CANDIDATES).contains(&count) {
            return Err(invalid());
        }
        let mut candidates = Vec::with_capacity(count);
        for _ in 0..count {
            candidates.push(ArchiveCandidate {
                relative: d.bytes()?,
                sha256: d.array()?,
            });
        }
        d.done()?;
        let value = Self {
            request,
            candidates,
        };
        value.validate()?;
        Ok(value)
    }
}

/// Only acceptance of a fixed source reader on the actual original Job. This
/// is NOT its result, a native closure, archive license or materialized input.
#[derive(Clone, PartialEq, Eq)]
pub struct SourceCaptureAccepted {
    pub selection_sha256: [u8; 32],
    pub remaining_input_ns: u64,
    pub context: ContextReply,
}
impl SourceCaptureAccepted {
    pub fn encode(&self, original: &SourceCapture) -> io::Result<Vec<u8>> {
        original.validate()?;
        if !matches!(self.remaining_input_ns, 1..=MAX_BUDGET_NS) {
            return Err(invalid());
        }
        fixed_context(&self.context, &original.request.key.graph)?;
        let mut e = Encoder::new(139);
        e.number(1);
        e.frame_bytes(&original.encode()?)?;
        e.0.extend(self.selection_sha256);
        e.number(self.remaining_input_ns);
        e.frame_bytes(&self.context.encode()?)?;
        e.finish()
    }
    pub fn decode(bytes: &[u8], original: &SourceCapture, digest: [u8; 32]) -> io::Result<Self> {
        original.validate()?;
        let mut d = header(bytes, 139)?;
        if d.number()? != 1 || SourceCapture::decode(&d.frame_bytes()?)? != *original {
            return Err(invalid());
        }
        let selection_sha256 = d.array()?;
        if selection_sha256 != digest {
            return Err(invalid());
        }
        let remaining_input_ns = d.number()?;
        let context = ContextReply::decode(&d.frame_bytes()?, &original.request.key.graph.query)?;
        d.done()?;
        let value = Self {
            selection_sha256,
            remaining_input_ns,
            context,
        };
        value.encode(original)?;
        Ok(value)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn selection() -> SourceCapture {
        SourceCapture {
            request: super::super::tests::request(),
            candidates: vec![ArchiveCandidate {
                relative: b"bootstrap/trust-stage0/dist/2026-11-01/seed.tar.xz".to_vec(),
                sha256: [7; 32],
            }],
        }
    }
    #[test]
    fn candidate_capture_is_bounded_exact_data_and_excludes_existing_profiles() {
        let value = selection();
        let bytes = value.encode().unwrap();
        assert!(SourceCapture::decode(&bytes).unwrap() == value);
        assert!(Request::decode(&bytes).is_err());
        assert!(super::super::super::query::Request::decode(&bytes).is_err());
        assert!(super::super::super::object::Request::decode(&bytes).is_err());
        for cut in 0..bytes.len() {
            assert!(SourceCapture::decode(&bytes[..cut]).is_err());
        }
        let mut extra = bytes;
        extra.push(0);
        assert!(SourceCapture::decode(&extra).is_err());
        let mut duplicate = value.clone();
        duplicate.candidates.push(value.candidates[0].clone());
        assert!(duplicate.encode().is_err());
        let mut empty = value.clone();
        empty.candidates.clear();
        assert!(empty.encode().is_err());
        for relative in [
            b"/outside".as_slice(),
            b"bootstrap/trust-stage0/dist/../seed.tar.xz",
            b"bootstrap/trust-stage0/dist/day/sub/seed.tar.xz",
        ] {
            let mut changed = value.clone();
            changed.candidates[0].relative = relative.to_vec();
            assert!(changed.encode().is_err());
        }
        let mut over = value;
        over.candidates = (0..=MAX_ARCHIVE_CANDIDATES)
            .map(|i| ArchiveCandidate {
                relative: format!("bootstrap/trust-stage0/dist/day/{i}.tar.xz").into_bytes(),
                sha256: [7; 32],
            })
            .collect();
        assert!(over.encode().is_err());
    }
    #[test]
    fn acceptance_binds_the_entire_population_original_context_digest_and_endpoint() {
        let original = selection();
        let value = SourceCaptureAccepted {
            selection_sha256: [9; 32],
            remaining_input_ns: 1,
            context: crate::bootstrap_graph::tests::context(),
        };
        let bytes = value.encode(&original).unwrap();
        assert!(SourceCaptureAccepted::decode(&bytes, &original, [9; 32]).unwrap() == value);
        assert!(SourceCaptureAccepted::decode(&bytes, &original, [8; 32]).is_err());
        let mut changed = original.clone();
        changed.candidates[0].sha256 = [8; 32];
        assert!(SourceCaptureAccepted::decode(&bytes, &changed, [9; 32]).is_err());
        for cut in 0..bytes.len() {
            assert!(SourceCaptureAccepted::decode(&bytes[..cut], &original, [9; 32]).is_err());
        }
        for remaining in [0, MAX_BUDGET_NS + 1] {
            assert!(
                SourceCaptureAccepted {
                    remaining_input_ns: remaining,
                    ..value.clone()
                }
                .encode(&original)
                .is_err()
            );
        }
    }
}
