//! Definition-body observations from the same completed fenced replay as the
//! seven type observations. These are comparison DATA, never proof authority.

use super::*;
use clean_kernel::env::{ConstantInfo, ConstantKind};

/// The independently emitted Lean value bytes use the existing bounded term
/// codec. The book names that domain explicitly; a digest is not a runtime pin.
pub const VF5_DEFINITION_VALUE_CODEC: &str = VF5_TARGET_TYPE_CODEC;

/// The repaired checker definitions whose bodies must be compared. Callers
/// cannot replace this roster with a favorable subset.
pub const VF5_DEFINITION_VALUE_TARGETS: &[&str] = &[
    "VF5.functionIdsUnique",
    "VF5.checkModuleC",
    "VF5.rowShape",
    "VF5.RowProved",
    "VF5.ValidBlob",
];

#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Vf5DefinitionValueMeasurement {
    pub name: Name,
    pub level_params: Vec<Name>,
    pub canonical_value_byte_len: usize,
    pub canonical_value_sha256: [u8; 32],
}

/// An independently derived expectation, not an accepted reference, certificate
/// or production pin. Unknown fields and a changed codec/roster are refused.
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Vf5DefinitionValueBook {
    pub codec: String,
    pub definition_values: Vec<Vf5DefinitionValueMeasurement>,
}

impl Vf5DefinitionValueBook {
    /// Compare the complete fixed five-definition book. Equality only describes
    /// observations; it cannot admit a mathematical base or a compiler row.
    #[must_use]
    pub fn matches(&self, actual: &[Vf5DefinitionValueMeasurement]) -> bool {
        self.codec == VF5_DEFINITION_VALUE_CODEC
            && actual.len() == VF5_DEFINITION_VALUE_TARGETS.len()
            && actual.iter().zip(VF5_DEFINITION_VALUE_TARGETS).all(|(row, target)| {
                row.name == Name::from_string(target) && row.canonical_value_byte_len != 0
            })
            && self.definition_values == actual
    }
}

#[derive(Debug)]
pub struct Vf5DefinitionValuesMeasurement {
    pub base: Vf5BaseMeasurement,
    pub definition_values: Vec<Vf5DefinitionValueMeasurement>,
}

/// Refusals preserve the original replay/resource boundary and distinguish a
/// missing definition from a declaration that has no observable definition body.
#[derive(Debug)]
pub enum Vf5DefinitionValueMiss {
    Measurement(Vf5MeasurementMiss),
    MissingDefinition { target: &'static str },
    NameMismatch { target: &'static str },
    NotDefinition { target: &'static str, kind: ConstantKind },
    MissingValue { target: &'static str },
    Duplicate { target: &'static str },
    Codec { target: &'static str, reason: String },
    EmptyEncoding { target: &'static str },
}

impl From<Vf5MeasurementMiss> for Vf5DefinitionValueMiss {
    fn from(error: Vf5MeasurementMiss) -> Self {
        Self::Measurement(error)
    }
}

impl From<Vf5BaseMiss> for Vf5DefinitionValueMiss {
    fn from(error: Vf5BaseMiss) -> Self {
        Self::Measurement(Vf5MeasurementMiss::Base(error))
    }
}

/// Replay once through the unchanged manifest, EMPTY-start, axiom and reference
/// fences. Observe seven types and five actual definition VALUES in that same
/// completed kernel, then drop it before returning DATA. In particular, the old
/// fixed248 world lacks `functionIdsUnique` and must refuse this new observation;
/// the existing type-only API still accepts exactly the packages it did before.
pub fn measure_package_with_definition_values(
    root: &Path,
) -> Result<Vf5DefinitionValuesMeasurement, Vf5DefinitionValueMiss> {
    let (kernel, base) = replay_for_observation(root)?;
    let definition_values = observe_values(&kernel, VF5_DEFINITION_VALUE_TARGETS, preparation_stop)?;
    drop(kernel);
    check_deadline()?;
    Ok(Vf5DefinitionValuesMeasurement { base, definition_values })
}

fn poll(stop: &mut dyn FnMut() -> Option<StopCause>) -> Result<(), Vf5DefinitionValueMiss> {
    stop().map_or(Ok(()), |cause| Err(Vf5BaseMiss::Stopped(cause).into()))
}

fn observe_values(
    kernel: &clean_kernel::ReferenceKernel,
    targets: &[&'static str],
    mut stop: impl FnMut() -> Option<StopCause>,
) -> Result<Vec<Vf5DefinitionValueMeasurement>, Vf5DefinitionValueMiss> {
    poll(&mut stop)?;
    let mut measured = Vec::new();
    measured.try_reserve(targets.len())
        .map_err(|error| Vf5BaseMiss::Io(std::io::Error::other(error)))?;
    let mut seen = BTreeSet::new();
    for &target in targets {
        poll(&mut stop)?;
        let name = Name::from_string(target);
        if !seen.insert(name.clone()) {
            return Err(Vf5DefinitionValueMiss::Duplicate { target });
        }
        let declaration = kernel.environment().get_const(&name)
            .ok_or(Vf5DefinitionValueMiss::MissingDefinition { target })?;
        measured.push(observe_definition(declaration, target, &mut stop)?);
    }
    poll(&mut stop)?;
    Ok(measured)
}

fn observe_definition(
    declaration: &ConstantInfo,
    target: &'static str,
    stop: &mut dyn FnMut() -> Option<StopCause>,
) -> Result<Vf5DefinitionValueMeasurement, Vf5DefinitionValueMiss> {
    poll(stop)?;
    if declaration.name != Name::from_string(target) {
        return Err(Vf5DefinitionValueMiss::NameMismatch { target });
    }
    if declaration.kind != ConstantKind::Definition {
        return Err(Vf5DefinitionValueMiss::NotDefinition { target, kind: declaration.kind });
    }
    let value = declaration.value.as_ref()
        .ok_or(Vf5DefinitionValueMiss::MissingValue { target })?;
    let mut level_params = Vec::new();
    level_params.try_reserve(declaration.level_params.len())
        .map_err(|error| Vf5BaseMiss::Io(std::io::Error::other(error)))?;
    for parameter in &declaration.level_params {
        poll(stop)?;
        level_params.push(parameter.clone());
    }
    poll(stop)?;
    // Use the maintained byte/node/depth bounds. Its synchronous encoder has no
    // internal stop callback, so a stop afterwards rejects the ENTIRE book.
    let bytes = serialize_term(value)
        .map_err(|error| Vf5DefinitionValueMiss::Codec { target, reason: format!("{error:?}") })?;
    poll(stop)?;
    if bytes.is_empty() {
        return Err(Vf5DefinitionValueMiss::EmptyEncoding { target });
    }
    let mut hash = Sha256::new();
    for chunk in bytes.chunks(4096) {
        poll(stop)?;
        hash.update(chunk);
    }
    poll(stop)?;
    Ok(Vf5DefinitionValueMeasurement {
        name: declaration.name.clone(), level_params,
        canonical_value_byte_len: bytes.len(), canonical_value_sha256: hash.finalize().into(),
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use clean_kernel::{BinderInfo, Declaration, Expr, Level};

    fn toy(shape: bool) -> clean_kernel::ReferenceKernel {
        crate::calculus_row::test_support::toy_kernel(shape)
    }

    #[test]
    fn equal_types_do_not_hide_different_checked_definition_values() {
        let left = toy(true);
        let right = toy(false);
        let target = ["VF5.rowShape"];
        let left_type = observe_types(&left, &target, || None).unwrap();
        let right_type = observe_types(&right, &target, || None).unwrap();
        assert_eq!(left_type, right_type, "same declared type is not a body commitment");
        let left_before = left.env_digest();
        let right_before = right.env_digest();
        let left_value = observe_values(&left, &target, || None).unwrap();
        let right_value = observe_values(&right, &target, || None).unwrap();
        assert_ne!(left_value[0].canonical_value_sha256, right_value[0].canonical_value_sha256);
        assert_eq!(left.env_digest(), left_before);
        assert_eq!(right.env_digest(), right_before);
    }

    #[test]
    fn definition_values_preserve_actual_universe_parameters() {
        let mut kernel = toy(true);
        let u = Name::from_string("u");
        let domain = Expr::sort(Level::param(u.clone()));
        kernel.add_checked(Declaration::Definition {
            name: Name::from_string("Observation.identity"), level_params: vec![u.clone()],
            type_: Expr::pi(BinderInfo::Default, domain.clone(),
                Expr::pi(BinderInfo::Default, Expr::bvar(0), Expr::bvar(1))),
            value: Expr::lam(BinderInfo::Default, domain,
                Expr::lam(BinderInfo::Default, Expr::bvar(0), Expr::bvar(0))),
            is_reducible: false,
        }).unwrap();
        let observed = observe_values(&kernel, &["Observation.identity"], || None).unwrap();
        assert_eq!(observed[0].level_params, vec![u]);
    }

    #[test]
    fn missing_theorem_opaque_and_duplicate_definitions_refuse_without_partial_book() {
        let mut kernel = toy(true);
        kernel.add_checked(Declaration::Opaque {
            name: Name::from_string("Observation.opaque"), level_params: vec![],
            type_: Expr::const_(Name::from_string("Nat"), vec![]), value: Expr::nat_lit(0),
        }).unwrap();
        assert!(matches!(observe_values(&kernel, VF5_DEFINITION_VALUE_TARGETS, || None),
            Err(Vf5DefinitionValueMiss::MissingDefinition { target: "VF5.functionIdsUnique" })));
        assert!(matches!(observe_values(&kernel, &["VF5.rowShape", "VF5.row_of"], || None),
            Err(Vf5DefinitionValueMiss::NotDefinition { kind: ConstantKind::Theorem, .. })));
        assert!(matches!(observe_values(&kernel, &["Observation.opaque"], || None),
            Err(Vf5DefinitionValueMiss::NotDefinition { kind: ConstantKind::Opaque, .. })));
        assert!(matches!(observe_values(&kernel, &["VF5.rowShape", "VF5.rowShape"], || None),
            Err(Vf5DefinitionValueMiss::Duplicate { target: "VF5.rowShape" })));
    }

    #[test]
    fn malformed_declaration_data_has_no_definition_value_observation() {
        // Defensive branch controls, not a claim that checked admission permits
        // a definition without its value or with another declaration's name.
        let mut declaration = ConstantInfo::new(Name::from_string("Observation.value"), vec![],
            Expr::const_(Name::from_string("Nat"), vec![]), None, false);
        assert!(matches!(observe_definition(&declaration, "Observation.value", &mut || None),
            Err(Vf5DefinitionValueMiss::MissingValue { .. })));
        declaration.value = Some(Expr::nat_lit(0));
        assert!(matches!(observe_definition(&declaration, "Observation.other", &mut || None),
            Err(Vf5DefinitionValueMiss::NameMismatch { .. })));
    }

    #[test]
    fn a_stop_at_any_value_observation_boundary_discards_the_book() {
        let kernel = toy(true);
        let targets = ["VF5.rowShape", "VF5.RowProved"];
        let mut total = 0;
        assert!(observe_values(&kernel, &targets, || { total += 1; None }).is_ok());
        for stop_at in 1..=total {
            let mut polls = 0;
            assert!(matches!(observe_values(&kernel, &targets, || {
                polls += 1; (polls == stop_at).then_some(StopCause::WallBackstop)
            }), Err(Vf5DefinitionValueMiss::Measurement(Vf5MeasurementMiss::Base(
                Vf5BaseMiss::Stopped(StopCause::WallBackstop))))), "poll {stop_at}");
        }
    }

    #[test]
    fn definition_measurement_preserves_stop_before_package_io() {
        let (_, stop) = crate::with_stop_scope(|| {
            crate::note_certify_stop(StopCause::WallBackstop);
            assert!(matches!(measure_package_with_definition_values(Path::new("/missing-definition-book")),
                Err(Vf5DefinitionValueMiss::Measurement(Vf5MeasurementMiss::Base(
                    Vf5BaseMiss::Stopped(StopCause::WallBackstop))))));
        });
        assert_eq!(stop, Some(StopCause::WallBackstop));
    }
}
