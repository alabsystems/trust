//! Consuming same-attempt local + native closure, never a token/record release.
use trust_resource_controller::FileIdentity;
use trust_resource_controller::bootstrap_graph::SourceRecord;
use trust_resource_controller::client::bootstrap_graph::InputWorkClosed;
use trust_sha2::{Digest as _, Sha256};

use super::super::LocalJoinedScope;
use super::*;
use crate::trust_repo_lock::management::lease::NamespaceGuard;

/// Issued only after the SAME joined local scope and opaque native closure
/// retire the actual original source publication. This retains their original
/// descriptions for final checks; it grants no active source lease or work.
#[must_use]
pub struct RetiredResidentInputs {
    source: OriginalSourceRoot,
    closed: InputWorkClosed,
}
impl RetiredResidentInputs {
    pub fn check_current(&self, deadline: Instant) -> io::Result<()> {
        check_retired_source(&self.source)?;
        self.closed
            .revalidate(deadline)
            .inspect_err(|error| self.source.inner.fail(error.to_string()))?;
        check_retired_source(&self.source)
    }
}

fn check_retired_source(source: &OriginalSourceRoot) -> io::Result<()> {
    // OPEN dispatcher/publication checks are intentionally unavailable after
    // retirement. Keep checking the SAME retained original directory instead
    // of reopening a path or accepting any replacement source namespace.
    let result = (|| {
        let state = source.inner.state()?;
        if state.phase != super::super::Phase::Joined || state.failure.is_some() {
            return Err(io::Error::other("retired input source has no clean joined scope"));
        }
        drop(state);
        source.inner.original.original.manager.root.check_current().map_err(io::Error::other)
    })();
    result.inspect_err(|error| source.inner.fail(error.to_string()))
}

#[must_use = "failed input retirement retains the actual original owners"]
pub struct RefusedInputRetirement {
    joined: LocalJoinedScope,
    source: OriginalSourceRoot,
    offer: OriginalSourceOffer,
    closed: InputWorkClosed,
    error: io::Error,
}
impl RefusedInputRetirement {
    pub fn error(&self) -> &io::Error {
        &self.error
    }
    pub fn into_parts(
        self,
    ) -> (LocalJoinedScope, OriginalSourceRoot, OriginalSourceOffer, InputWorkClosed, io::Error)
    {
        (self.joined, self.source, self.offer, self.closed, self.error)
    }
}
impl std::fmt::Debug for RefusedInputRetirement {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("RefusedInputRetirement").field("error", &self.error).finish_non_exhaustive()
    }
}
fn validate_offer(
    offer: &OriginalSourceOffer,
    expected: &trust_resource_controller::bootstrap_graph::SourceAttachment,
) -> io::Result<()> {
    let data = &offer.data;
    let metadata = description_metadata(&offer.files)?;
    let id = |m: &Metadata| {
        use std::os::unix::fs::MetadataExt as _;
        FileIdentity { device: m.dev(), inode: m.ino() }
    };
    let record = |index: usize, bytes: &[u8]| SourceRecord {
        identity: id(&metadata[index]),
        bytes: bytes.len() as u64,
        sha256: Sha256::digest(bytes).into(),
    };
    if expected.source_directory != id(&metadata[0])
        || expected.holder_directory != id(&metadata[1])
        || expected.holder_name != data.holder_leaf().as_bytes()
        || expected.original_record != record(2, data.original_record())
        || expected.withheld_record != record(3, data.withheld_record())
        || record_bytes(&offer.files[2])? != data.original_record()
        || record_bytes(&offer.files[3])? != data.withheld_record()
    {
        return Err(io::Error::other(
            "native input closure is not this exact original source offer",
        ));
    }
    Ok(())
}

// Shared actual joined-source validation. Binding DATA alone grants no native
// closure or directory borrow; the public borrow below additionally requires
// opaque InputWorkClosed and its exact original source-offer binding.
fn validate_joined_source(
    joined: &LocalJoinedScope,
    source: &OriginalSourceRoot,
    offer: &OriginalSourceOffer,
    expected: &trust_resource_controller::bootstrap_graph::SourceAttachment,
) -> io::Result<()> {
    let result = (|| {
        joined.check_current()?;
        if !Arc::ptr_eq(&joined.inner, &source.inner) || !Arc::ptr_eq(&joined.inner, &offer.inner) {
            return Err(io::Error::other("joined input source has another original scope"));
        }
        check_retired_source(source)?;
        source.inner.original.check_current()?;
        validate_offer(offer, expected)?;
        check_retired_source(source)?;
        joined.check_current()
    })();
    result.inspect_err(|error| source.inner.fail(error.to_string()))
}

impl OriginalSourceRoot {
    /// Borrow the SAME original directory for final input checks after local
    /// join and actual native source-work closure. OPEN dispatcher checks are
    /// intentionally unavailable here. The original source directory is never
    /// reopened or replaced. This grants no new work, source retirement, Seed
    /// or SDK authority.
    pub fn joined_input_directory(
        &self,
        joined: &LocalJoinedScope,
        offer: &OriginalSourceOffer,
        closed: &InputWorkClosed,
    ) -> io::Result<std::os::fd::BorrowedFd<'_>> {
        let result: io::Result<std::os::fd::BorrowedFd<'_>> = (|| {
            closed.revalidate(self.inner.deadline)?;
            validate_joined_source(joined, self, offer, closed.source())?;
            closed.revalidate(self.inner.deadline)?;
            validate_joined_source(joined, self, offer, closed.source())?;
            Ok(self.inner.original.original.manager.root.file.as_fd())
        })();
        result.inspect_err(|error| self.inner.fail(error.to_string()))
    }
}

impl LocalJoinedScope {
    /// Retire only this actual original WITHHELD publication. Local joins,
    /// input observations and serialized Closed frames cannot call this path:
    /// it additionally consumes the opaque SAME pinned native input closure.
    /// No original Root/GNU/SDK owner is retired by this operation.
    pub fn retire_resident_inputs(
        self,
        source: OriginalSourceRoot,
        offer: OriginalSourceOffer,
        closed: InputWorkClosed,
    ) -> Result<RetiredResidentInputs, Box<RefusedInputRetirement>> {
        let actual = (|| {
            self.check_current()?;
            closed.revalidate(self.inner.deadline)?;
            if !Arc::ptr_eq(&self.inner, &source.inner)
                || !Arc::ptr_eq(&self.inner, &offer.inner)
                || Arc::strong_count(&self.inner) != 3
                || Arc::strong_count(&self.inner.original) != 1
            {
                return Err(io::Error::other(
                    "original input scope still has another actual borrower",
                ));
            }
            // OriginalSourceRoot::check_current requires an OPEN dispatcher.
            // Here it is deliberately JOINED: validate the SAME underlying
            // original namespace/records and offered descriptions directly.
            let original = &self.inner.original;
            validate_joined_source(&self, &source, &offer, closed.source())?;
            let manager = &original.original.manager;
            let _namespace = NamespaceGuard::acquire(&manager.root.physical)?;
            // Validate exact retained current publication while holding the
            // SAME kernel namespace lock. Never convert WITHHELD to ordinary
            // token release or let a census/adoption record replace lineage.
            manager.check_record(&original.held)?;
            if !manager.writers(None)?.is_empty() || !manager.writers(None)?.is_empty() {
                return Err(io::Error::other(
                    "a surviving or uncertain source writer prevents input retirement",
                ));
            }
            closed.revalidate(self.inner.deadline)?;
            manager.check_record(&original.held)?;
            manager.retire(&original.held)?;
            manager.root.file.sync_all()
        })();
        match actual {
            Ok(()) => Ok(RetiredResidentInputs { source, closed }),
            Err(error) => {
                Err(Box::new(RefusedInputRetirement { joined: self, source, offer, closed, error }))
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use std::time::{Duration, Instant};

    use super::*;
    use crate::trust_repo_lock::management::{Acquire, Kind, LeaseAcquisition, Manager};
    fn original() -> (tempfile::TempDir, ProtectedWorkScope, OriginalSourceRoot, OriginalSourceOffer)
    {
        let root = tempfile::tempdir().unwrap();
        let request = Acquire {
            kind: Kind::Build,
            owner_pid: std::process::id(),
            purpose: "actual resident source retirement binding".into(),
            contract: "no closure from binding data".into(),
            wait: Duration::ZERO,
            inherited_token: None,
            break_reason: None,
        };
        let LeaseAcquisition::Granted(lease) =
            Manager::open(root.path()).unwrap().acquire_lease(&request).unwrap()
        else {
            panic!("fixture busy");
        };
        let scope = ProtectedWorkScope::new(
            Arc::new(lease.into_withheld().unwrap()),
            Instant::now() + Duration::from_secs(60),
        )
        .unwrap();
        let source = scope.original_source(root.path()).unwrap();
        let offer = source.close_only_offer().unwrap();
        (root, scope, source, offer)
    }
    fn expected(
        offer: &OriginalSourceOffer,
    ) -> trust_resource_controller::bootstrap_graph::SourceAttachment {
        use std::os::unix::fs::MetadataExt as _;
        let m = offer.data.description_metadata();
        let id = |n: usize| FileIdentity { device: m[n].dev(), inode: m[n].ino() };
        let record = |n: usize, bytes: &[u8]| SourceRecord {
            identity: id(n),
            bytes: bytes.len() as u64,
            sha256: Sha256::digest(bytes).into(),
        };
        trust_resource_controller::bootstrap_graph::SourceAttachment {
            key: trust_resource_controller::bootstrap_graph::Key {
                query: trust_resource_controller::ContextQuery {
                    binding: trust_resource_controller::JobBinding {
                        session: "s-abcd".into(),
                        root_attempt: [1; 16],
                        capability: [2; 32],
                    },
                    call_attempt: [3; 16],
                },
                graph: [4; 16],
            },
            source_directory: id(0),
            holder_directory: id(1),
            holder_name: offer.data.holder_leaf().as_bytes().to_vec(),
            original_record: record(2, offer.data.original_record()),
            withheld_record: record(3, offer.data.withheld_record()),
        }
    }
    #[test]
    fn same_actual_source_offer_binding_survives_local_join_but_never_releases() {
        let (root, scope, source, offer) = original();
        let data = expected(&offer);
        scope.seal().join().unwrap().check_current().unwrap();
        validate_offer(&offer, &data).unwrap();
        drop(source);
        drop(offer);
        assert!(!Manager::open(root.path()).unwrap().status().unwrap().is_free());
    }
    #[test]
    fn altered_native_binding_or_actual_record_bytes_refuse_and_leave_withheld() {
        let (root, scope, _source, offer) = original();
        let data = expected(&offer);
        let mut wrong = data.clone();
        wrong.withheld_record.sha256[0] ^= 1;
        assert!(validate_offer(&offer, &wrong).is_err());
        let mut wrong = data.clone();
        wrong.original_record.identity.inode += 1;
        assert!(validate_offer(&offer, &wrong).is_err());
        let info = root.path().join(".trust-build-lock/info");
        let mut bytes = std::fs::read(&info).unwrap();
        bytes[0] ^= 1;
        std::fs::write(&info, &bytes).unwrap();
        assert!(validate_offer(&offer, &data).is_err());
        drop(scope);
        assert!(root.path().join(".trust-build-lock").exists());
    }

    #[test]
    fn joined_source_namespace_check_never_reopens_or_releases_the_original() {
        let (root, scope, source, offer) = original();
        let joined = scope.seal().join().unwrap();
        joined.check_current().unwrap();
        check_retired_source(&source).unwrap();
        // This helper checks a held directory, not native closure or release.
        assert!(!Manager::open(root.path()).unwrap().status().unwrap().is_free());

        let displaced = root.path().with_extension("retained-source");
        std::fs::rename(root.path(), &displaced).unwrap();
        std::fs::create_dir(root.path()).unwrap();
        assert!(check_retired_source(&source).is_err());
        std::fs::remove_dir(root.path()).unwrap();
        std::fs::rename(&displaced, root.path()).unwrap();
        assert!(check_retired_source(&source).is_err(), "namespace failure remains latched");
        drop(joined);
        drop(source);
        drop(offer);
        assert!(!Manager::open(root.path()).unwrap().status().unwrap().is_free());
    }

    #[test]
    fn joined_offer_validation_preserves_original_descriptions_without_open_dispatch() {
        let (root, scope, source, offer) = original();
        let data = expected(&offer);
        let directory = source.directory().unwrap();
        let raw = directory.as_raw_fd();
        let flags = unsafe { libc::fcntl(raw, libc::F_GETFL) };
        let local = unsafe { libc::fcntl(raw, libc::F_GETFD) };
        let joined = scope.seal().join().unwrap();
        // Exercise the actual joined/offer primitives without fabricating the
        // opaque native closure required by joined_input_directory/retirement.
        validate_joined_source(&joined, &source, &offer, &data).unwrap();
        assert_eq!(directory.as_raw_fd(), raw);
        assert_eq!(unsafe { libc::fcntl(raw, libc::F_GETFL) }, flags);
        assert_eq!(unsafe { libc::fcntl(raw, libc::F_GETFD) }, local);
        assert!(!Manager::open(root.path()).unwrap().status().unwrap().is_free());
    }

    #[test]
    fn joined_validation_rejects_foreign_scope_and_altered_offer_without_revival() {
        for foreign in [false, true] {
            let (root, scope, source, offer) = original();
            let data = expected(&offer);
            let joined = scope.seal().join().unwrap();
            if foreign {
                let (_other, scope, _source, _offer) = original();
                let other_joined = scope.seal().join().unwrap();
                assert!(validate_joined_source(&other_joined, &source, &offer, &data).is_err());
            } else {
                let mut wrong = data.clone();
                wrong.withheld_record.sha256[0] ^= 1;
                assert!(validate_joined_source(&joined, &source, &offer, &wrong).is_err());
            }
            assert!(validate_joined_source(&joined, &source, &offer, &data).is_err());
            assert!(!Manager::open(root.path()).unwrap().status().unwrap().is_free());
        }
    }
}
