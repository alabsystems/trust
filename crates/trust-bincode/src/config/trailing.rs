// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Trailing-byte policy. Transcribed from `bincode-1.3.3/src/config/trailing.rs`.
//!
//! NOTE the asymmetry, which is the incumbent's and is preserved deliberately:
//! this check is applied ONLY on the slice path (`Options::deserialize`). A
//! `deserialize_from` over an `io::Read`er never runs it, so `reject_trailing_bytes()`
//! has no effect there.

use crate::de::read::SliceReader;
use crate::error::{ErrorKind, Result};

/// A trait for erroring deserialization if not all bytes were read.
pub trait TrailingBytes {
    /// Checks a given slice reader to determine if deserialization used all
    /// bytes in the slice.
    fn check_end(reader: &SliceReader<'_>) -> Result<()>;
}

/// A `TrailingBytes` config that will allow trailing bytes in slices after
/// deserialization.
#[derive(Copy, Clone)]
pub struct AllowTrailing;

/// A `TrailingBytes` config that will cause an error if bytes are left over in
/// the slice when deserialization is complete.
#[derive(Copy, Clone)]
pub struct RejectTrailing;

impl TrailingBytes for AllowTrailing {
    #[inline(always)]
    fn check_end(_reader: &SliceReader<'_>) -> Result<()> {
        Ok(())
    }
}

impl TrailingBytes for RejectTrailing {
    #[inline(always)]
    fn check_end(reader: &SliceReader<'_>) -> Result<()> {
        if reader.is_finished() {
            Ok(())
        } else {
            Err(Box::new(ErrorKind::Custom(
                "Slice had bytes remaining after deserialization".to_string(),
            )))
        }
    }
}
