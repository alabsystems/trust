//! Private one-use maintenance custody, never a general WITHHELD release API.
//! The canonical record remains WITHHELD throughout maintenance. Only the
//! same native probe can restore its local idle original lease; no ACTIVE
//! publication/error rollback window can erase durable in-flight exclusion.

use std::sync::Arc;

use super::*;
use crate::admission::cache_probe::NativeClosed;

#[derive(Clone)]
pub(crate) struct Binding(Arc<()>);
impl Binding {
    pub(crate) fn same(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.0, &other.0)
    }
}
pub(crate) struct State {
    original: Box<HeldRecord>,
    binding: Binding,
    idle: bool,
}
#[must_use = "retain durable maintenance exclusion until the same actual probe closes"]
pub(crate) struct MaintenanceLease {
    original: Lease,
}
#[must_use = "failed maintenance transition retains original exclusion"]
pub(crate) struct Failure {
    _original: Option<Box<Lease>>,
    _withholding: Option<WithholdFailure>,
    error: io::Error,
}
impl Failure {
    fn original(original: Lease, error: io::Error) -> Self {
        Self { _original: Some(Box::new(original)), _withholding: None, error }
    }
}
impl fmt::Debug for Failure {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("MaintenanceFailure").field(&self.error).finish()
    }
}
impl fmt::Display for Failure {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "maintenance custody retained: {}", self.error)
    }
}
impl std::error::Error for Failure {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        Some(&self.error)
    }
}

impl MaintenanceLease {
    pub(crate) fn begin(mut original: Lease) -> Result<Self, Failure> {
        original.release_on_drop = false;
        let binding = Binding(Arc::new(()));
        if let Some(state) = original.maintenance.as_mut() {
            let idle = state.idle;
            // Poison before every fallible action. No failed check returns the
            // previous idle proof or permits ordinary destructor release.
            state.idle = false;
            state.binding = binding;
            let checked = if idle {
                check_original(&original)
            } else {
                Err(invalid("maintenance operation is already unresolved"))
            };
            return match checked {
                Ok(()) => Ok(Self { original }),
                Err(error) => Err(Failure::original(original, error)),
            };
        }
        let WithheldLease { mut original, held, protected_scope: _ } =
            match original.into_withheld() {
                Ok(held) => held,
                Err(held) => {
                    let error = io::Error::other(held.to_string());
                    return Err(Failure { _original: None, _withholding: Some(held), error });
                }
            };
        // Move the SAME descriptions. Nothing is reopened, flocked or minted
        // from text; retain the original now-unlinked ACTIVE record as input.
        let old = std::mem::replace(&mut original.held, Box::new(held));
        original.maintenance = Some(Box::new(State { original: old, binding, idle: false }));
        Ok(Self { original })
    }
    pub(crate) fn binding(&self) -> Binding {
        self.original.maintenance.as_ref().expect("same maintenance").binding.clone()
    }
    pub(crate) fn check_current(&self) -> io::Result<()> {
        check_original(&self.original)
    }
    pub(crate) fn restore(mut self, closed: NativeClosed) -> Result<Lease, Failure> {
        let result = (|| {
            self.check_current()?;
            let state = self.original.maintenance.as_ref().expect("same maintenance");
            if state.idle || !closed.matches(&state.binding) {
                return Err(invalid(
                    "maintenance closure does not belong to this original private probe",
                ));
            }
            Ok(())
        })();
        if let Err(error) = result {
            return Err(Failure::original(self.original, error));
        }
        // No IO after this local transition and no canonical record mutation.
        // Producer death at any point still leaves the durable WITHHELD row.
        self.original.maintenance.as_mut().expect("same maintenance").idle = true;
        self.original.release_on_drop = true;
        Ok(self.original)
    }
}

fn check_original(original: &Lease) -> io::Result<()> {
    original.check_current()?;
    check_pinned(original)
}
fn check_pinned(original: &Lease) -> io::Result<()> {
    let state = original
        .maintenance
        .as_ref()
        .ok_or_else(|| invalid("original maintenance state missing"))?;
    check_original_description(&state.original)?;
    if original.process != std::process::id()
        || original.borrowed
        || !original.held.parse()?.is_withheld()
    {
        return Err(invalid("maintenance lost its same-process independent withheld owner"));
    }
    original.manager.check_record(&original.held)
}

impl Lease {
    /// Only Lease::release_original calls this for the private local idle state
    /// restored by this operation's actual NativeClosed token. Generic token
    /// release, WITHHELD import/recovery and Host release remain unavailable.
    pub(in crate::trust_repo_lock::management::lease) fn release_maintenance(
        &self,
    ) -> io::Result<super::super::Release> {
        check_pinned(self)?;
        if !self.maintenance.as_ref().expect("same maintenance").idle {
            return Err(invalid("in-flight native maintenance cannot retire its holder"));
        }
        // release_original already holds the SAME namespace transaction.
        // Keep uncertain/surviving writers as durable debt; do not convert the
        // row to an adoptable ACTIVE record even on this final failure path.
        if !self.manager.writers(None)?.is_empty() || !self.manager.writers(None)?.is_empty() {
            return Err(invalid("surviving or uncertain writer retains maintenance exclusion"));
        }
        self.manager.check_record(&self.held)?;
        self.manager.retire(&self.held)?;
        Ok(super::super::Release::Released)
    }
}
