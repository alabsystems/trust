// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates

//! Distinct configured-selection DATA, never a source/configuration owner.
//! Frame126 stays byte-for-byte unchanged. No client/Host accepts frame127
//! until its distinct supported operation also retains the actual caller and
//! configuration-root issuers. In particular, a decoded parser input must be
//! validated again by Bootstrap's existing parser and FullEnvelope contract.
use super::*;

pub const MAX_ARGUMENTS: usize = 1024;
pub const MAX_ARGUMENT_BYTES: usize = 64 * 1024;

/// Exact original parser input and cwd observations, not executable argv.
/// Only Bootstrap classifies this DATA with its existing Flags parser; the
/// shared codec deliberately has no flag parser, evaluator or dispatch API.
#[derive(Clone, PartialEq, Eq)]
pub struct ConfigurationSelection {
    pub parser_input: Vec<String>,
    pub invocation_directory: Vec<u8>,
}
impl ConfigurationSelection {
    pub fn validate(&self) -> io::Result<()> {
        if self.parser_input.is_empty()
            || self.parser_input.len() > MAX_ARGUMENTS
            || !absolute(&self.invocation_directory)
        {
            return Err(invalid());
        }
        self.parser_input
            .iter()
            .try_fold(0usize, |total, argument| {
                if argument.as_bytes().contains(&0) {
                    return None;
                }
                total.checked_add(argument.len()).and_then(|bytes| bytes.checked_add(1))
            })
            .filter(|bytes| *bytes <= MAX_ARGUMENT_BYTES)
            .ok_or_else(invalid)?;
        Ok(())
    }
    fn write(&self, encoder: &mut Encoder) -> io::Result<()> {
        self.validate()?;
        encoder.bytes(&self.invocation_directory)?;
        encoder.number(self.parser_input.len() as u64);
        for argument in &self.parser_input {
            encoder.bytes(argument.as_bytes())?;
        }
        Ok(())
    }
    fn read(decoder: &mut Decoder<'_>) -> io::Result<Self> {
        let invocation_directory = decoder.bytes()?;
        let count = decoder.count(MAX_ARGUMENTS)?;
        let mut parser_input = Vec::with_capacity(count);
        // Bound the complete parser input before allocating each argument,
        // rather than applying only the codec's independent per-field bound.
        let mut bytes = 0usize;
        for _ in 0..count {
            let length = decoder.count(MAX_ARGUMENT_BYTES)?;
            bytes = bytes
                .checked_add(length)
                .and_then(|total| total.checked_add(1))
                .filter(|total| *total <= MAX_ARGUMENT_BYTES)
                .ok_or_else(invalid)?;
            let argument = std::str::from_utf8(decoder.take(length)?).map_err(|_| invalid())?;
            parser_input.push(argument.to_owned());
        }
        let value = Self { parser_input, invocation_directory };
        value.validate()?;
        Ok(value)
    }
}

/// Future explicit capability/version. It cannot be downgraded to a126
/// submission or125 reply without losing its original configuration selection.
/// No sender, receiver, source owner or external-file offer is enabled here.
#[derive(Clone, PartialEq, Eq)]
pub struct ConfiguredIntentSelection {
    pub selection: IntentSelection,
    pub configuration: ConfigurationSelection,
}
impl ConfiguredIntentSelection {
    pub fn validate(&self) -> io::Result<()> {
        self.selection.validate()?;
        self.configuration.validate()
    }
    pub fn encode(&self) -> io::Result<Vec<u8>> {
        self.validate()?;
        let mut encoder = Encoder::new(127);
        encoder.number(1);
        self.selection.write(&mut encoder)?;
        self.configuration.write(&mut encoder)?;
        encoder.finish()
    }
    pub fn decode(bytes: &[u8]) -> io::Result<Self> {
        let mut decoder = header(bytes, 127)?;
        if decoder.number()? != 1 {
            return Err(invalid());
        }
        let value = Self {
            selection: IntentSelection::read(&mut decoder)?,
            configuration: ConfigurationSelection::read(&mut decoder)?,
        };
        decoder.done()?;
        value.validate()?;
        Ok(value)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn configured() -> ConfiguredIntentSelection {
        ConfiguredIntentSelection {
            selection: super::super::tests::intent().selection,
            configuration: ConfigurationSelection {
                invocation_directory: b"/original-cwd".to_vec(),
                parser_input: [
                    "build",
                    "--config",
                    "/external/full.toml",
                    "--set",
                    "profile=\"compiler\"",
                    "--set",
                    "build.jobs=2",
                    "--set",
                    "build.jobs=1",
                    "--build-dir",
                    "/output",
                ]
                .map(str::to_owned)
                .to_vec(),
            },
        }
    }
    #[test]
    fn exact_original_selection_order_and_empty_fields_roundtrip_without_downgrade() {
        let value = configured();
        let old126 = value.selection.encode().unwrap();
        let bytes = value.encode().unwrap();
        assert!(ConfiguredIntentSelection::decode(&bytes).unwrap() == value);
        assert!(IntentSelection::decode(&old126).unwrap() == value.selection);
        assert!(IntentSelection::decode(&bytes).is_err());
        assert!(ConfiguredIntentSelection::decode(&old126).is_err());
        let query = IntentQuery { key: super::super::super::tests::request().key.graph };
        assert!(IntentReply::decode(&bytes, &query).is_err());
        assert!(Request::decode(&bytes).is_err());
        let mut empty = value;
        empty.configuration.parser_input.push(String::new());
        assert!(ConfiguredIntentSelection::decode(&empty.encode().unwrap()).unwrap() == empty);
    }
    #[test]
    fn configured_frames_refuse_versions_truncation_trailing_or_non_utf8_parser_data() {
        let bytes = configured().encode().unwrap();
        for end in 0..bytes.len() {
            assert!(ConfiguredIntentSelection::decode(&bytes[..end]).is_err());
        }
        let mut bad = bytes.clone();
        bad[23] = 2;
        assert!(ConfiguredIntentSelection::decode(&bad).is_err());
        let mut bad = bytes.clone();
        bad.push(0);
        assert!(ConfiguredIntentSelection::decode(&bad).is_err());
        let mut bad = bytes;
        let index = bad.windows(5).position(|part| part == b"build").unwrap();
        bad[index] = 255;
        assert!(ConfiguredIntentSelection::decode(&bad).is_err());
    }
    #[test]
    fn complete_argument_bound_and_cwd_syntax_never_create_a_configuration_owner() {
        for arguments in [
            vec![],
            vec!["build".to_owned(); MAX_ARGUMENTS + 1],
            vec!["x".repeat(MAX_ARGUMENT_BYTES)],
            vec!["x".repeat(MAX_ARGUMENT_BYTES / 2); 2],
            vec!["build".to_owned(), "bad\0path".to_owned()],
        ] {
            let mut bad = configured();
            bad.configuration.parser_input = arguments;
            assert!(bad.encode().is_err());
        }
        for cwd in [b"relative".as_slice(), b"/cwd/../other", b"/cwd//other", b"/cwd\0"] {
            let mut bad = configured();
            bad.configuration.invocation_directory = cwd.to_vec();
            assert!(bad.encode().is_err());
        }
        // Codec syntax deliberately accepts unknown Flags: only the SAME
        // Bootstrap parser can classify/refuse them before any real issuer.
        let mut unknown = configured();
        unknown.configuration.parser_input = vec!["--unknown-option".into()];
        assert!(ConfiguredIntentSelection::decode(&unknown.encode().unwrap()).is_ok());
    }
}
