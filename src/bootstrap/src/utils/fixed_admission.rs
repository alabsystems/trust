//! Trust: retain an actual original fixed admission before configuration.
//! No integer, marker or saved record constructs this owner. The original
//! outer group remains the signal/retirement owner throughout Bootstrap.

use std::ffi::OsString;
use std::sync::{Arc, OnceLock};

use build_helper::admission::{EarlyFixedClaim, FIXED_HANDOFF_ENV, InheritedFixedClaim};

static ORIGINAL: OnceLock<Result<Option<Arc<InheritedFixedClaim>>, String>> = OnceLock::new();

pub struct Early {
    direct: Option<EarlyFixedClaim>,
    courier: Option<OsString>,
}

/// Observation only, before the GNU importer can allocate/reuse descriptors.
pub fn snapshot_at_entry() -> Result<Early, String> {
    let direct = std::env::var_os(FIXED_HANDOFF_ENV);
    let courier = std::env::var_os(jobserver_utils::FIXED_CLAIM_HANDOFF_ENV);
    if courier.is_some() {
        if direct.as_deref() != Some(std::ffi::OsStr::new("requires-live-ancestor-v1")) {
            return Err("fixed original courier requires its old-reader refusal sentinel".into());
        }
        Ok(Early { direct: None, courier })
    } else {
        let direct = direct
            .as_deref()
            .map(EarlyFixedClaim::snapshot)
            .transpose()
            .map_err(|error| error.to_string())?;
        Ok(Early { direct, courier: None })
    }
}

/// Called after the one early GNU capture and before arbitrary callbacks.
pub fn capture_at_entry(early: Early) -> Result<(), String> {
    if ORIGINAL.get().is_some() {
        return Err("fixed Bootstrap admission was already captured".into());
    }
    let actual = match (early.direct, early.courier) {
        (Some(direct), None) => direct.capture().map(Some),
        (None, Some(courier)) => InheritedFixedClaim::from_descendant(&courier).map(Some),
        (None, None) => Ok(None),
        _ => unreachable!("snapshot rejects mixed fixed inputs"),
    }
    .map(|actual| actual.map(Arc::new))
    .map_err(|error| error.to_string());
    ORIGINAL.set(actual).map_err(|_| "fixed Bootstrap capture raced".to_owned())?;
    budget().map(|_| ())
}

pub(crate) fn budget() -> Result<Option<u32>, String> {
    match ORIGINAL.get() {
        Some(Ok(Some(original))) => {
            original.budget().map(|budget| Some(budget.get())).map_err(|error| error.to_string())
        }
        Some(Ok(None)) => Ok(None),
        Some(Err(error)) => Err(error.clone()),
        None if std::env::var_os(FIXED_HANDOFF_ENV).is_some()
            || std::env::var_os(jobserver_utils::FIXED_CLAIM_HANDOFF_ENV).is_some() =>
        {
            Err("fixed Bootstrap mode requires original native entry capture".into())
        }
        None => Ok(None),
    }
}
