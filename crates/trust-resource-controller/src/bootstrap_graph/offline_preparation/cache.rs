// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates

//! Same-carrier acknowledgement DATA for the original caller cache directory.
//! Neither this reply nor Request constructs an actual cache-lock owner.
use super::*;
use crate::{ContextReply, bootstrap_graph::fixed_context};

#[derive(Clone, PartialEq, Eq)]
pub enum PreparationCacheReply {
    Prepared {
        request: Request,
        request_sha256: [u8; 32],
        remaining_input_ns: u64,
        context: ContextReply,
    },
    Custodied {
        request: Request,
        request_sha256: [u8; 32],
        remaining_input_ns: u64,
        context: ContextReply,
    },
}
impl PreparationCacheReply {
    pub fn encode(&self) -> io::Result<Vec<u8>> {
        let (request, digest, remaining, context) = match self {
            Self::Prepared {
                request,
                request_sha256,
                remaining_input_ns,
                context,
            }
            | Self::Custodied {
                request,
                request_sha256,
                remaining_input_ns,
                context,
            } => (request, request_sha256, remaining_input_ns, context),
        };
        if !matches!(*remaining, 1..=MAX_BUDGET_NS) {
            return Err(invalid());
        }
        fixed_context(context, &request.key.graph)?;
        let mut e = Encoder::new(137);
        e.number(1);
        e.number(u64::from(matches!(self, Self::Custodied { .. })));
        e.frame_bytes(&request.encode()?)?;
        e.0.extend(digest);
        e.number(*remaining);
        e.frame_bytes(&context.encode()?)?;
        e.finish()
    }
    pub fn decode(bytes: &[u8], original: &Request, expected_sha256: [u8; 32]) -> io::Result<Self> {
        original.validate()?;
        let mut d = header(bytes, 137)?;
        if d.number()? != 1 {
            return Err(invalid());
        }
        let kind = d.number()?;
        let request = Request::decode(&d.frame_bytes()?)?;
        let request_sha256 = d.array()?;
        if request != *original || request_sha256 != expected_sha256 {
            return Err(invalid());
        }
        let remaining_input_ns = d.number()?;
        let context = ContextReply::decode(&d.frame_bytes()?, &request.key.graph.query)?;
        d.done()?;
        let value = match kind {
            0 => Self::Prepared {
                request,
                request_sha256,
                remaining_input_ns,
                context,
            },
            1 => Self::Custodied {
                request,
                request_sha256,
                remaining_input_ns,
                context,
            },
            _ => return Err(invalid()),
        };
        value.encode()?;
        Ok(value)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn reply_binds_whole_original_request_context_digest_and_remaining_endpoint() {
        let request = super::super::tests::request();
        let digest = [0x39; 32];
        for reply in [
            PreparationCacheReply::Prepared {
                request: request.clone(),
                request_sha256: digest,
                remaining_input_ns: MAX_BUDGET_NS,
                context: crate::bootstrap_graph::tests::context(),
            },
            PreparationCacheReply::Custodied {
                request: request.clone(),
                request_sha256: digest,
                remaining_input_ns: 1,
                context: crate::bootstrap_graph::tests::context(),
            },
        ] {
            let bytes = reply.encode().unwrap();
            assert!(PreparationCacheReply::decode(&bytes, &request, digest).unwrap() == reply);
            assert!(PreparationCacheReply::decode(&bytes, &request, [0x40; 32]).is_err());
            let mut foreign = request.clone();
            foreign.cargo_home = b"/another-home".to_vec();
            assert!(PreparationCacheReply::decode(&bytes, &foreign, digest).is_err());
            for cut in 0..bytes.len() {
                assert!(PreparationCacheReply::decode(&bytes[..cut], &request, digest).is_err());
            }
            let mut trailing = bytes;
            trailing.push(0);
            assert!(PreparationCacheReply::decode(&trailing, &request, digest).is_err());
        }
        for remaining in [0, MAX_BUDGET_NS + 1] {
            let reply = PreparationCacheReply::Custodied {
                request: request.clone(),
                request_sha256: digest,
                remaining_input_ns: remaining,
                context: crate::bootstrap_graph::tests::context(),
            };
            assert!(reply.encode().is_err());
        }
    }
}
