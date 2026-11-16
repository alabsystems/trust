// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Measure a source-bound VF5 package without admitting a production base.
//! Run through the declared toolchain and canonical heavy-job admission.

use std::path::PathBuf;
use std::process::ExitCode;
use trust_certify::calculus_row::base::measurement::{
    VF5_TARGET_TYPE_CODEC, Vf5TargetTypeMeasurement, measure_package_with_target_types,
};

fn main() -> ExitCode {
    let mut args = std::env::args_os().skip(1);
    let Some(root) = args.next() else {
        eprintln!("usage: measure_vf5_base PACKAGE_ROOT [--expect-target-types INDEPENDENT_BOOK.json]");
        return ExitCode::from(2);
    };
    let expected = match args.next() {
        None => None,
        Some(flag) if flag == "--expect-target-types" => match args.next() {
            Some(path) if args.next().is_none() => Some(PathBuf::from(path)),
            _ => { eprintln!("--expect-target-types needs exactly one independent JSON array"); return ExitCode::from(2); }
        },
        Some(_) => { eprintln!("unexpected measurement argument"); return ExitCode::from(2); }
    };
    match measure_package_with_target_types(&PathBuf::from(root)) {
        Ok(measurement) => {
            if let Some(path) = expected {
                let expected = trust_proof_session::storage::read_bounded(&path)
                    .map_err(|error| error.to_string())
                    .and_then(|bytes| serde_json::from_slice::<Vec<Vf5TargetTypeMeasurement>>(&bytes)
                        .map_err(|error| error.to_string()));
                match expected {
                    Ok(expected) if type_book_matches(&measurement.target_types, &expected) => {}
                    Ok(_) => {
                        eprintln!("VF5 base measurement refused: actual production target types differ from the independent book");
                        return ExitCode::FAILURE;
                    }
                    Err(error) => {
                        eprintln!("VF5 independent target book unreadable or malformed: {error}");
                        return ExitCode::FAILURE;
                    }
                }
            }
            let report = measurement.report;
            println!(
                "{}",
                serde_json::json!({
                    "kind": "vf5-base-measurement-v1",
                    "manifest_sha256": hex(&report.manifest_sha256),
                    "environment_sha256": hex(&report.environment.0),
                    "captured_modules": report.captured_modules,
                    "replay": report.replay,
                    "target_type_codec": VF5_TARGET_TYPE_CODEC,
                    "target_types": measurement.target_types,
                    "production_admission": false,
                })
            );
            ExitCode::SUCCESS
        }
        Err(error) => {
            eprintln!("VF5 base measurement refused: {error:?}");
            ExitCode::FAILURE
        }
    }
}

/// Diagnostic DATA comparison only. Equal observations cannot create a pin,
/// accepted kernel entry, certificate or successful compiler policy decision.
fn type_book_matches(actual: &[Vf5TargetTypeMeasurement], expected: &[Vf5TargetTypeMeasurement]) -> bool {
    actual.len() == 7 && actual == expected
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|byte| format!("{byte:02x}")).collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use clean_kernel::name::Name;

    fn data_book() -> Vec<Vf5TargetTypeMeasurement> {
        // Comparison DATA, never an observed production kernel or pin.
        ["VF5.RowProved", "VF5.row_of", "VF5.checkBlob", "VF5.rowShape",
         "VF5.vc_sound_F1", "VF5.compose_F1", "VF5.rootsSafe_of"].into_iter().map(|name| {
            Vf5TargetTypeMeasurement {
                name: Name::from_string(name), level_params: vec![Name::from_string("u")],
                canonical_type_byte_len: 10, canonical_type_sha256: [1; 32],
            }
        }).collect()
    }

    #[test]
    fn independent_type_book_mismatch_is_not_a_successful_measurement() {
        let actual = data_book();
        assert!(type_book_matches(&actual, &actual));
        let mut changed = actual.clone(); changed[0].canonical_type_sha256[0] ^= 1;
        assert!(!type_book_matches(&actual, &changed));
        let mut changed = actual.clone(); changed[1].level_params.push(Name::from_string("v"));
        assert!(!type_book_matches(&actual, &changed));
        let mut changed = actual.clone(); changed[2].canonical_type_byte_len += 1;
        assert!(!type_book_matches(&actual, &changed));
        let mut changed = actual.clone(); changed[3].name = Name::from_string("VF5.other");
        assert!(!type_book_matches(&actual, &changed));
        let mut changed = actual.clone(); changed.swap(0, 1);
        assert!(!type_book_matches(&actual, &changed));
        assert!(!type_book_matches(&actual, &actual[..6]));
        assert!(!type_book_matches(&[], &[]), "absence/partial output grants no diagnostic success");
    }
}
