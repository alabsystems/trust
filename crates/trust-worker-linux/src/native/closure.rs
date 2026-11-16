use sha2::{Digest, Sha256};
use trust_process_isolation::{Binding, Budget, Charge, Phase, Session, SessionOwner};

use super::{ALIASES, NAME, OBJECTS, PATH, charge, check, contract, elf, reserve};
use crate::Error;
use crate::launcher::{InputClosureIdentity, InputIdentity, InputSource, snapshot};

/// Literal aliases are virtual capability names, never paths opened by this
/// service. The owner must establish artifact/runtime provenance separately.
#[derive(Debug, Clone, Copy)]
pub struct NativeObjectPlan<'a> {
    pub source: InputSource<'a>,
    pub role: NativeRole,
    pub soname: &'a str,
    pub needed: &'a [&'a str],
    pub aliases: &'a [&'a str],
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NativeRole {
    Macro,
    Runtime,
    Dependency,
}

#[derive(Debug)]
pub(super) struct Object {
    pub snapshot: snapshot::Snapshot,
    pub role: NativeRole,
    pub soname: Vec<u8>,
    pub needed: Vec<Vec<u8>>,
    pub aliases: Vec<Vec<u8>>,
}

/// Prepared immutable inputs only. This does not say a worker loaded or
/// consumed them, nor that constructors or native execution were contained.
#[derive(Debug)]
pub struct NativeInputReceipt {
    pub identity: InputClosureIdentity,
    pub graph_digest: [u8; 32],
    pub input_bytes: u64,
    pub objects: Vec<NativeObjectReceipt>,
}

#[derive(Debug)]
pub struct NativeObjectReceipt {
    pub input: InputIdentity,
    pub role: NativeRole,
    pub soname: Vec<u8>,
    pub needed: Vec<Vec<u8>>,
    pub aliases: Vec<Vec<u8>>,
}

/// Exact copied bytes and graph bound to one owner invocation and allowance.
/// No native loader, symbol/bridge admission or proof claim is provided.
#[derive(Debug)]
pub struct NativeClosure {
    pub(super) objects: Vec<Object>,
    pub(super) binding: Binding,
    pub(super) budget: Budget,
    session_owner: SessionOwner,
    identity: InputClosureIdentity,
    digest: [u8; 32],
    input_bytes: u64,
    // Allocate receipt bookkeeping under the original grant before launch.
    receipt_objects: Vec<NativeObjectReceipt>,
}

/// Broker-local immutable bytes only. This cannot stand in for the original
/// compiler SessionOwner. A trusted bootstrap must independently bind its graph
/// and prepaid allowance to that parent's exact invocation before service.
#[derive(Debug)]
pub(super) struct Inventory {
    pub objects: Vec<Object>,
    pub budget: Budget,
}
impl From<NativeClosure> for Inventory {
    fn from(closure: NativeClosure) -> Self {
        Self { objects: closure.objects, budget: closure.budget }
    }
}
impl Inventory {
    pub fn prepare_delegated(
        plans: &[NativeObjectPlan<'_>],
        expected: [u8; 32],
        max: u64,
        budget: &Budget,
    ) -> Result<Self, Error> {
        let result = (|| {
            if expected == [0; 32] || digest(plans, max, budget)? != expected {
                return Err(contract(budget, "delegated native graph identity"));
            }
            let (objects, _) = snapshot_objects(plans, budget)?;
            check(budget)?;
            Ok(Self { objects, budget: budget.clone() })
        })();
        if result.is_err() {
            budget.refuse(trust_process_isolation::Error::Phase);
        }
        result
    }
}

fn snapshot_objects(
    plans: &[NativeObjectPlan<'_>],
    budget: &Budget,
) -> Result<(Vec<Object>, u64), Error> {
    let mut objects = reserve(plans.len(), budget)?;
    let mut input_bytes = 0u64;
    for plan in plans {
        check(budget)?;
        let snapshot = snapshot::copy(&plan.source, budget)?;
        elf::admit(&snapshot, plan, budget)?;
        input_bytes = input_bytes
            .checked_add(snapshot.size)
            .ok_or_else(|| contract(budget, "native input bytes overflow"))?;
        let soname = bytes(plan.soname.as_bytes(), budget)?;
        let mut needed = reserve(plan.needed.len(), budget)?;
        for value in plan.needed {
            needed.push(bytes(value.as_bytes(), budget)?);
        }
        let mut aliases = reserve(plan.aliases.len(), budget)?;
        for value in plan.aliases {
            aliases.push(bytes(value.as_bytes(), budget)?);
        }
        objects.push(Object { snapshot, role: plan.role, soname, needed, aliases });
    }
    Ok((objects, input_bytes))
}

impl NativeClosure {
    /// The grant exists before source opens. The identity includes the planned
    /// static worker inputs, which B3 must independently match before launch.
    pub fn prepare(
        plans: &[NativeObjectPlan<'_>],
        identity: InputClosureIdentity,
        session: &Session,
        max_input_bytes: u64,
    ) -> Result<Self, Error> {
        let budget = session.budget().clone();
        let binding = session.binding().clone();
        let result = (|| {
            check(&budget)?;
            charge(&budget, Charge { work: 1024, ..Charge::default() })?;
            binding.validate().map_err(|e| Error::Budget(budget.refuse(e)))?;
            let digest = digest(plans, max_input_bytes, &budget)?;
            if session.phase() != Phase::AwaitReady
                || identity.native_graph() != Some(digest)
                || binding.input_closure != identity.digest()
                || plans
                    .iter()
                    .find(|p| p.role == NativeRole::Macro)
                    .is_none_or(|p| p.source.sha256 != binding.artifact)
            {
                return Err(contract(&budget, "native closure binding"));
            }
            let receipt_objects = reserve(plans.len(), &budget)?;
            let (objects, input_bytes) = snapshot_objects(plans, &budget)?;
            check(&budget)?;
            Ok(Self {
                objects,
                binding,
                budget: budget.clone(),
                session_owner: session.owner(),
                identity,
                digest,
                input_bytes,
                receipt_objects,
            })
        })();
        if result.is_err() {
            budget.refuse(trust_process_isolation::Error::Phase);
        }
        result
    }
    pub fn digest(&self) -> [u8; 32] {
        self.digest
    }
    pub fn object_count(&self) -> usize {
        self.objects.len()
    }
    pub fn binding(&self) -> &Binding {
        &self.binding
    }
    pub(crate) fn input_bytes(&self) -> u64 {
        self.input_bytes
    }
    pub(crate) fn check_data_inputs(
        &self,
        inputs: &[Option<snapshot::Snapshot>],
    ) -> Result<(), Error> {
        if inputs.len() != self.objects.len()
            || inputs.iter().zip(&self.objects).any(|(input, object)| {
                input.as_ref().is_none_or(|input| {
                    input.sha256 != object.snapshot.sha256
                        || input.size != object.snapshot.size
                        || input.executable
                })
            })
        {
            return Err(contract(
                &self.budget,
                "native static inputs must be exact sealed graph data",
            ));
        }
        check(&self.budget)
    }
    pub(crate) fn check_invocation(
        &self,
        identity: &InputClosureIdentity,
        session: &Session,
    ) -> Result<(), Error> {
        check(&self.budget)?;
        if !self.session_owner.matches(session)
            || !self.budget.shares_owner(session.budget())
            || session.binding() != &self.binding
            || session.phase() != Phase::AwaitReady
            || identity != &self.identity
            || identity.digest() != self.binding.input_closure
        {
            return Err(Error::Budget(
                self.budget.refuse(trust_process_isolation::Error::Identity),
            ));
        }
        Ok(())
    }

    pub(crate) fn into_receipt(mut self) -> NativeInputReceipt {
        // Capacity was reserved during preparation. Moving the already bounded
        // graph needs neither a new grant nor allocation after child teardown.
        for object in self.objects {
            self.receipt_objects.push(NativeObjectReceipt {
                input: InputIdentity {
                    sha256: object.snapshot.sha256,
                    size: object.snapshot.size,
                    executable: object.snapshot.executable,
                },
                role: object.role,
                soname: object.soname,
                needed: object.needed,
                aliases: object.aliases,
            });
        }
        NativeInputReceipt {
            identity: self.identity,
            graph_digest: self.digest,
            input_bytes: self.input_bytes,
            objects: self.receipt_objects,
        }
    }
}

/// Domain-separated owner-plan digest, with finite structural validation before
/// hashing. It includes all graph/alias identities and the initial bank policy.
pub fn digest(plans: &[NativeObjectPlan<'_>], max: u64, b: &Budget) -> Result<[u8; 32], Error> {
    check(b)?;
    if plans.is_empty() || plans.len() > OBJECTS || max == 0 {
        return Err(contract(b, "native closure bounds"));
    }
    let mut total = 0u64;
    charge(b, Charge { work: plans.len() as u64, ..Charge::default() })?;
    if plans.iter().filter(|p| p.role == NativeRole::Macro).count() != 1 {
        return Err(contract(b, "native macro root"));
    }
    for (at, p) in plans.iter().enumerate() {
        charge(b, Charge { values: 1, work: 128, ..Charge::default() })?;
        if !p.source.executable
            || p.source.sha256 == [0; 32]
            || p.source.size == 0
            || !name(p.soname)
            || p.needed.len() > OBJECTS
            || p.aliases.is_empty()
            || p.aliases.len() > ALIASES
        {
            return Err(contract(b, "native object plan"));
        }
        total =
            total.checked_add(p.source.size).ok_or_else(|| contract(b, "native input overflow"))?;
        if total > max {
            return Err(contract(b, "native input bytes"));
        }
        for (i, n) in p.needed.iter().enumerate() {
            if n.len() > NAME {
                return Err(contract(b, "native needed length"));
            }
            charge(b, Charge { work: (n.len() + plans.len() * NAME) as u64, ..Charge::default() })?;
            if !name(n)
                || p.needed[..i].contains(n)
                || plans.iter().filter(|q| q.soname == *n).count() != 1
            {
                return Err(contract(b, "native needed identity"));
            }
        }
        for (n, alias) in p.aliases.iter().enumerate() {
            if alias.len() > PATH {
                return Err(contract(b, "native alias length"));
            }
            charge(
                b,
                Charge {
                    work: (4 * alias.len() + at * ALIASES * PATH + n * PATH) as u64,
                    ..Charge::default()
                },
            )?;
            if !path(alias)
                || p.aliases[..n].contains(alias)
                || plans[..at].iter().any(|q| q.aliases.contains(alias))
            {
                return Err(contract(b, "native alias identity"));
            }
        }
        charge(b, Charge { work: (at * NAME) as u64, ..Charge::default() })?;
        if plans[..at].iter().any(|q| q.soname == p.soname) {
            return Err(contract(b, "duplicate native SONAME"));
        }
    }
    let mut h = Sha256::new();
    h.update(b"trust-native-object-closure-v1\0bank33-63-once\0");
    h.update((plans.len() as u64).to_le_bytes());
    for p in plans {
        charge(b, Charge { work: 64 + p.soname.len() as u64, ..Charge::default() })?;
        h.update(p.source.sha256);
        h.update(p.source.size.to_le_bytes());
        h.update([match p.role {
            NativeRole::Macro => 0,
            NativeRole::Runtime => 1,
            NativeRole::Dependency => 2,
        }]);
        field(&mut h, p.soname.as_bytes());
        for list in [p.needed, p.aliases] {
            h.update((list.len() as u64).to_le_bytes());
            for s in list {
                charge(b, Charge { work: s.len() as u64 + 8, ..Charge::default() })?;
                field(&mut h, s.as_bytes());
            }
        }
    }
    check(b)?;
    Ok(h.finalize().into())
}
fn field(h: &mut Sha256, s: &[u8]) {
    h.update((s.len() as u64).to_le_bytes());
    h.update(s);
}
fn name(s: &str) -> bool {
    !s.is_empty()
        && s.len() <= NAME
        && s.bytes().all(|c| c.is_ascii_alphanumeric() || b"._+-".contains(&c))
}
fn path(s: &str) -> bool {
    s.len() > 1
        && s.len() <= PATH
        && s.starts_with('/')
        && s.bytes().all(|c| c.is_ascii_graphic() && c != b'\\')
        && s.split('/').skip(1).all(|part| !part.is_empty() && part != "." && part != "..")
}
fn bytes(s: &[u8], b: &Budget) -> Result<Vec<u8>, Error> {
    charge(b, Charge { work: s.len() as u64, ..Charge::default() })?;
    let mut result = reserve(s.len(), b)?;
    result.extend_from_slice(s);
    Ok(result)
}
