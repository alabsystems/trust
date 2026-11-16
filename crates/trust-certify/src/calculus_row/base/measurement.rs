//! Additive observation of the ACTUAL completed production replay. These
//! hashes describe declaration TYPES, not a checked closed goal/proof digest.
//! No reference, accepted certificate, runtime pin or grade leaves this API.

use super::*;
use clean_auto::bridge::ay_contract::serialize_term;

mod definitions;
pub use definitions::{
    VF5_DEFINITION_VALUE_CODEC, VF5_DEFINITION_VALUE_TARGETS, Vf5DefinitionValueBook,
    Vf5DefinitionValueMeasurement, Vf5DefinitionValueMiss, Vf5DefinitionValuesMeasurement,
    measure_package_with_definition_values,
};

mod judgments;
pub use judgments::{
    Vf5AcceptedRowData, Vf5JudgmentInput, Vf5JudgmentObservation, Vf5JudgmentsMeasurement,
    measure_package_with_judgments,
};

/// The existing bounded canonical term codec, with domain/version carried by
/// this measurement envelope. Its bytes are not a CertifiedPayload.
pub const VF5_TARGET_TYPE_CODEC: &str =
    "clean_auto::bridge::ay_contract::serialize_term/bincode2-standard";

/// Structural names preserve universe-parameter identity without display /
/// reparse aliases. Deserializing this DATA cannot admit a reference or row.
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Vf5TargetTypeMeasurement {
    pub name: Name,
    pub level_params: Vec<Name>,
    pub canonical_type_byte_len: usize,
    pub canonical_type_sha256: [u8; 32],
}

#[derive(Debug)]
pub struct Vf5BaseMeasurement {
    pub report: Vf5BaseReport,
    pub target_types: Vec<Vf5TargetTypeMeasurement>,
}

/// A failed DATA observation. Base intake keeps its original refusal type; a
/// target observation error cannot construct a production reference or pin.
#[derive(Debug)]
pub enum Vf5MeasurementMiss {
    Base(Vf5BaseMiss),
    Target { target: &'static str, reason: String },
}

impl From<Vf5BaseMiss> for Vf5MeasurementMiss {
    fn from(error: Vf5BaseMiss) -> Self {
        Self::Base(error)
    }
}

/// Perform the SAME manifest capture and seven-target EMPTY-start replay as
/// production, then inspect that actual completed kernel before dropping it.
/// The older report-only measurement and every production admission path are
/// unchanged. Neither API accepts a caller-supplied digest as a runtime pin.
pub fn measure_package_with_target_types(root: &Path) -> Result<Vf5BaseMeasurement, Vf5MeasurementMiss> {
    let (kernel, measurement) = replay_for_observation(root)?;
    drop(kernel);
    check_deadline()?;
    Ok(measurement)
}

fn replay_for_observation(
    root: &Path,
) -> Result<(clean_kernel::ReferenceKernel, Vf5BaseMeasurement), Vf5MeasurementMiss> {
    check_deadline()?;
    let (root, bytes) = manifest_bytes(root)?;
    check_deadline()?;
    let manifest: Manifest = serde_json::from_slice(&bytes).map_err(Vf5BaseMiss::Manifest)?;
    validate_manifest(&manifest)?;
    let (kernel, report) = replay(&root, &manifest, Sha256::digest(&bytes).into())?;
    let target_types = observe_types(&kernel, TARGETS, preparation_stop)?;
    check_deadline()?;
    // Only private observation code borrows this actual completed kernel.
    // Neither public observation API returns it or constructs a Vf5Reference.
    Ok((kernel, Vf5BaseMeasurement { report, target_types }))
}

fn observe_types(
    kernel: &clean_kernel::ReferenceKernel,
    targets: &[&'static str],
    mut stop: impl FnMut() -> Option<StopCause>,
) -> Result<Vec<Vf5TargetTypeMeasurement>, Vf5MeasurementMiss> {
    let poll = |stop: &mut dyn FnMut() -> Option<StopCause>| -> Result<(), Vf5MeasurementMiss> {
        stop().map_or(Ok(()), |cause| Err(Vf5MeasurementMiss::Base(Vf5BaseMiss::Stopped(cause))))
    };
    poll(&mut stop)?;
    let mut measured = Vec::new();
    measured.try_reserve(targets.len())
        .map_err(|error| Vf5BaseMiss::Io(std::io::Error::other(error)))?;
    let mut seen = BTreeSet::new();
    for &target in targets {
        poll(&mut stop)?;
        let name = Name::from_string(target);
        if !seen.insert(name.clone()) {
            return Err(Vf5MeasurementMiss::Target { target, reason: "duplicate target".into() });
        }
        let declaration = kernel.environment().get_const(&name)
            .ok_or_else(|| Vf5MeasurementMiss::Target { target, reason: "completed kernel is missing target".into() })?;
        if declaration.name != name {
            return Err(Vf5MeasurementMiss::Target { target, reason: "target/declaration name mismatch".into() });
        }
        let mut level_params = Vec::new();
        level_params.try_reserve(declaration.level_params.len())
            .map_err(|error| Vf5BaseMiss::Io(std::io::Error::other(error)))?;
        for parameter in &declaration.level_params {
            poll(&mut stop)?;
            level_params.push(parameter.clone());
        }
        poll(&mut stop)?;
        // The maintained encoder enforces byte, structural-node and depth
        // bounds. It has no mid-call poll, so an actual inherited stop after
        // encoding refuses the ENTIRE measurement, never a partial success.
        let bytes = serialize_term(&declaration.type_)
            .map_err(|error| Vf5MeasurementMiss::Target { target, reason: format!("bounded type codec: {error:?}") })?;
        poll(&mut stop)?;
        if bytes.is_empty() {
            return Err(Vf5MeasurementMiss::Target { target, reason: "empty canonical type encoding".into() });
        }
        let mut hash = Sha256::new();
        for chunk in bytes.chunks(4096) {
            poll(&mut stop)?;
            hash.update(chunk);
        }
        poll(&mut stop)?;
        measured.push(Vf5TargetTypeMeasurement {
            name: declaration.name.clone(), level_params,
            canonical_type_byte_len: bytes.len(), canonical_type_sha256: hash.finalize().into(),
        });
    }
    poll(&mut stop)?;
    Ok(measured)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn actual_reference_types_use_exact_canonical_codec_and_universe_parameters() {
        // An existing unit-only stand-in reference tests observation mechanics;
        // it is NOT the production seven-target package or an enabling pin.
        let reference = super::super::super::test_support::pinned_toy(true);
        let kernel = &reference.kernel;
        let before = kernel.env_digest();
        let measured = observe_types(kernel, &["Eq", "VF5.RowProved", "VF5.row_of"], || None).unwrap();
        assert!(!measured[0].level_params.is_empty(), "real polymorphic declaration control");
        for (row, target) in measured.iter().zip(["Eq", "VF5.RowProved", "VF5.row_of"]) {
            let actual = kernel.environment().get_const(&Name::from_string(target)).unwrap();
            let bytes = serialize_term(&actual.type_).unwrap();
            assert_eq!(row.name, actual.name);
            assert_eq!(row.level_params, actual.level_params);
            assert_eq!(row.canonical_type_byte_len, bytes.len());
            assert_eq!(row.canonical_type_sha256, <[u8; 32]>::from(Sha256::digest(&bytes)));
        }
        assert_eq!(kernel.env_digest(), before, "observation never changes the kernel");
    }

    #[test]
    fn missing_production_target_or_duplicate_never_returns_partial_measurement() {
        let reference = super::super::super::test_support::pinned_toy(true);
        assert!(matches!(observe_types(&reference.kernel, TARGETS, || None),
            Err(Vf5MeasurementMiss::Target { target: "VF5.vc_sound_F1", .. })));
        assert!(matches!(observe_types(&reference.kernel, &["VF5.RowProved", "VF5.RowProved"], || None),
            Err(Vf5MeasurementMiss::Target { reason, .. }) if reason == "duplicate target"));
    }

    #[test]
    fn stop_at_each_observation_boundary_discards_the_entire_type_book() {
        let reference = super::super::super::test_support::pinned_toy(true);
        let targets = ["VF5.RowProved", "VF5.row_of"];
        let mut total = 0;
        assert!(observe_types(&reference.kernel, &targets, || { total += 1; None }).is_ok());
        for stop_at in 1..=total {
            let mut polls = 0;
            assert!(matches!(observe_types(&reference.kernel, &targets, || {
                polls += 1;
                (polls == stop_at).then_some(StopCause::WallBackstop)
            }), Err(Vf5MeasurementMiss::Base(Vf5BaseMiss::Stopped(StopCause::WallBackstop)))), "poll {stop_at}");
        }
    }

    #[test]
    fn measurement_preserves_an_existing_stop_before_package_io() {
        let (_, stop) = crate::with_stop_scope(|| {
            crate::note_certify_stop(StopCause::WallBackstop);
            assert!(matches!(
                measure_package_with_target_types(Path::new("/missing-vf5-measurement-stop-control")),
                Err(Vf5MeasurementMiss::Base(Vf5BaseMiss::Stopped(StopCause::WallBackstop))),
            ));
        });
        assert_eq!(stop, Some(StopCause::WallBackstop));
    }

    #[test]
    fn measurement_observes_an_earlier_inherited_clock_before_package_io() {
        let mut refused = false;
        let _outer = clean_kernel::tc::run_until(Some(Instant::now()), || {
            refused = matches!(
                measure_package_with_target_types(Path::new("/missing-vf5-measurement-deadline-control")),
                Err(Vf5MeasurementMiss::Base(Vf5BaseMiss::Stopped(StopCause::WallBackstop))),
            );
        });
        assert!(refused);
    }
}
