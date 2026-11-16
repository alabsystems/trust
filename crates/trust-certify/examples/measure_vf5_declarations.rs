// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Compare independently derived definition-body DATA with observations from
//! one completed fenced replay. This never admits a production reference.
//! The JSON book is {"codec": VF5_DEFINITION_VALUE_CODEC,
//! "definition_values": [the five ordered name/level_params/length/SHA rows]}.

use std::path::PathBuf;
use std::process::ExitCode;
use trust_certify::calculus_row::base::measurement::{
    VF5_DEFINITION_VALUE_CODEC, VF5_TARGET_TYPE_CODEC, Vf5DefinitionValueBook,
    measure_package_with_definition_values,
};

fn main() -> ExitCode {
    let mut args = std::env::args_os().skip(1);
    let (Some(root), Some(flag), Some(expected)) = (args.next(), args.next(), args.next()) else {
        eprintln!("usage: measure_vf5_declarations PACKAGE_ROOT --expect-definition-values INDEPENDENT_BOOK.json");
        return ExitCode::from(2);
    };
    if flag != "--expect-definition-values" || args.next().is_some() {
        eprintln!("expected exactly --expect-definition-values and one independent JSON book");
        return ExitCode::from(2);
    }
    let expected = trust_proof_session::storage::read_bounded(&PathBuf::from(expected))
        .map_err(|error| error.to_string())
        .and_then(|bytes| serde_json::from_slice::<Vf5DefinitionValueBook>(&bytes)
            .map_err(|error| error.to_string()));
    let expected = match expected {
        Ok(book) => book,
        Err(error) => {
            eprintln!("VF5 independent definition book unreadable or malformed: {error}");
            return ExitCode::FAILURE;
        }
    };
    match measure_package_with_definition_values(&PathBuf::from(root)) {
        Ok(measurement) => {
            if !expected.matches(&measurement.definition_values) {
                eprintln!("VF5 definition observation refused: actual definition values differ from the complete independent book or codec");
                return ExitCode::FAILURE;
            }
            let report = measurement.base.report;
            println!("{}", serde_json::json!({
                "kind": "vf5-definition-values-measurement-v1",
                "manifest_sha256": hex(&report.manifest_sha256),
                "environment_sha256": hex(&report.environment.0),
                "captured_modules": report.captured_modules,
                "replay": report.replay,
                "target_type_codec": VF5_TARGET_TYPE_CODEC,
                "target_types": measurement.base.target_types,
                "definition_value_codec": VF5_DEFINITION_VALUE_CODEC,
                "definition_values": measurement.definition_values,
                "definition_book_matched": true,
                "production_admission": false,
            }));
            ExitCode::SUCCESS
        }
        Err(error) => {
            eprintln!("VF5 definition observation refused: {error:?}");
            ExitCode::FAILURE
        }
    }
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|byte| format!("{byte:02x}")).collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use clean_kernel::name::Name;
    use trust_certify::calculus_row::base::measurement::{
        VF5_DEFINITION_VALUE_TARGETS, Vf5DefinitionValueMeasurement,
    };

    fn data_book() -> Vf5DefinitionValueBook {
        // Comparison DATA only, not a measured production environment or pin.
        Vf5DefinitionValueBook {
            codec: VF5_DEFINITION_VALUE_CODEC.into(),
            definition_values: VF5_DEFINITION_VALUE_TARGETS.iter().map(|name| {
                Vf5DefinitionValueMeasurement {
                    name: Name::from_string(name), level_params: vec![],
                    canonical_value_byte_len: 10, canonical_value_sha256: [1; 32],
                }
            }).collect(),
        }
    }

    #[test]
    fn independent_value_book_cannot_change_roster_codec_or_observed_values() {
        let expected = data_book();
        let actual = expected.definition_values.clone();
        assert!(expected.matches(&actual));
        let mut changed = expected.clone(); changed.codec.push_str("/other");
        assert!(!changed.matches(&actual));
        let mut changed = expected.clone(); changed.definition_values[0].canonical_value_sha256[0] ^= 1;
        assert!(!changed.matches(&actual));
        let mut changed = expected.clone(); changed.definition_values[1].canonical_value_byte_len += 1;
        assert!(!changed.matches(&actual));
        let mut changed = expected.clone(); changed.definition_values[2].level_params.push(Name::from_string("u"));
        assert!(!changed.matches(&actual));
        let mut changed = actual.clone(); changed[3].name = Name::from_string("VF5.other");
        assert!(!expected.matches(&changed));
        assert!(!expected.matches(&actual[..4]));
        assert!(!expected.matches(&[]));
        let mut changed = actual.clone(); changed.swap(0, 1);
        let changed_book = Vf5DefinitionValueBook {
            codec: VF5_DEFINITION_VALUE_CODEC.into(), definition_values: changed.clone(),
        };
        assert!(!changed_book.matches(&changed), "even matching reordered DATA is not the fixed roster");
        let mut changed = actual.clone(); changed[1] = changed[0].clone();
        let changed_book = Vf5DefinitionValueBook {
            codec: VF5_DEFINITION_VALUE_CODEC.into(), definition_values: changed.clone(),
        };
        assert!(!changed_book.matches(&changed), "matching duplicate rows cannot shrink the denominator");
    }
}
