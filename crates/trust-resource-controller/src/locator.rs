// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates

use std::io;

use crate::JobBinding;
use crate::wire::invalid;

fn hex<const N: usize>(text: &str) -> io::Result<[u8; N]> {
    if text.len() != 2 * N {
        return Err(invalid());
    }
    let digit = |byte: u8| match byte {
        b'0'..=b'9' => Ok(byte - b'0'),
        b'a'..=b'f' => Ok(byte - b'a' + 10),
        _ => Err(invalid()),
    };
    let mut result = [0; N];
    for (index, pair) in text.as_bytes().as_chunks::<2>().0.iter().enumerate() {
        result[index] = (digit(pair[0])? << 4) | digit(pair[1])?;
    }
    Ok(result)
}
fn write_hex(output: &mut String, bytes: &[u8]) {
    const DIGITS: &[u8; 16] = b"0123456789abcdef";
    for byte in bytes {
        output.push(DIGITS[(byte >> 4) as usize] as char);
        output.push(DIGITS[(byte & 15) as usize] as char);
    }
}
impl JobBinding {
    /// Decode the untrusted private environment locator. No authority is gained.
    pub fn from_locator(value: &str) -> io::Result<Self> {
        if value.len() > 165 {
            return Err(invalid());
        }
        let fields: Vec<_> = value.split(':').collect();
        if fields.len() != 4 || fields[0] != "v3" {
            return Err(invalid());
        }
        let binding = Self {
            session: fields[1].into(),
            root_attempt: hex(fields[2])?,
            capability: hex(fields[3])?,
        };
        binding.validate()?;
        Ok(binding)
    }
    /// Encode only for private inherited environment delivery. Never log it.
    pub fn locator(&self) -> io::Result<String> {
        self.validate()?;
        let mut value = format!("v3:{}:", self.session);
        write_hex(&mut value, &self.root_attempt);
        value.push(':');
        write_hex(&mut value, &self.capability);
        Ok(value)
    }
}
