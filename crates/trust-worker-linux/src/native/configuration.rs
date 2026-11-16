//! Bounded structural native bootstrap data. Its graph and static component
//! must recompute the original composite Binding before any constructor.
use std::fs::File;
use std::os::fd::FromRawFd;

use trust_process_isolation::{
    Binding, Budget, Charge, Envelope, Message, Phase, Session, SessionOwner,
};

use super::closure::Inventory;
use super::{
    ALIASES, NAME, NativeClosure, NativeObjectPlan, NativeObjectReceipt, NativeRole, OBJECTS, PATH,
    charge, check, contract, digest, io, reserve,
};
use crate::launcher::{InputClosureIdentity, InputIdentity, InputSource};
use crate::{Error, PinnedInput};

const MAX: usize = 512 * 1024;
pub(crate) struct Configuration {
    bytes: Vec<u8>,
    owner: SessionOwner,
    budget: Budget,
    binding: Binding,
    pub objects: [Option<InputIdentity>; OBJECTS],
    pub graph: Option<[u8; 32]>,
    pub required: [bool; OBJECTS],
}
impl Configuration {
    pub(crate) fn prepare(
        worker: InputIdentity,
        max: u64,
        native: Option<&NativeClosure>,
        session: &Session,
    ) -> Result<Self, Error> {
        let b = session.budget();
        check(b)?;
        if max == 0
            || max == u64::MAX
            || worker.size == 0
            || !worker.executable
            || worker.sha256 != session.binding().worker
            || session.phase() != Phase::AwaitReady
        {
            return Err(contract(b, "native configuration allowance/phase"));
        }
        let mut bytes = reserve(MAX, b)?;
        append(&mut bytes, b"NCFGv001", b)?;
        append(&mut bytes, &worker.size.to_le_bytes(), b)?;
        append(&mut bytes, &max.to_le_bytes(), b)?;
        append(&mut bytes, &native.map_or([0; 32], NativeClosure::digest), b)?;
        append(&mut bytes, &[native.map_or(0, NativeClosure::object_count) as u8], b)?;
        let mut objects = [None; OBJECTS];
        let mut root = None;
        if let Some(native) = native {
            for (at, object) in native.objects.iter().enumerate() {
                objects[at] = Some(InputIdentity {
                    sha256: object.snapshot.sha256,
                    size: object.snapshot.size,
                    executable: true,
                });
                if object.role == NativeRole::Macro {
                    root = Some(at);
                }
                append(&mut bytes, &object.snapshot.sha256, b)?;
                append(&mut bytes, &object.snapshot.size.to_le_bytes(), b)?;
                append(
                    &mut bytes,
                    &[match object.role {
                        NativeRole::Macro => 0,
                        NativeRole::Runtime => 1,
                        NativeRole::Dependency => 2,
                    }],
                    b,
                )?;
                field(&mut bytes, &object.soname, b)?;
                for list in [&object.needed, &object.aliases] {
                    append(&mut bytes, &[list.len() as u8], b)?;
                    for value in list {
                        field(&mut bytes, value, b)?;
                    }
                }
            }
        }
        let mut required = [false; OBJECTS];
        if let (Some(native), Some(root)) = (native, root) {
            required[root] = true;
            for _ in 0..OBJECTS {
                let mut changed = false;
                for (at, object) in native.objects.iter().enumerate() {
                    if required[at] {
                        for name in &object.needed {
                            charge(
                                b,
                                Charge {
                                    work: (native.objects.len() * NAME + 64) as u64,
                                    ..Charge::default()
                                },
                            )?;
                            let target = native
                                .objects
                                .iter()
                                .position(|object| &object.soname == name)
                                .ok_or_else(|| contract(b, "native required dependency"))?;
                            changed |= !required[target];
                            required[target] = true;
                        }
                    }
                }
                if !changed {
                    break;
                }
            }
        }
        Ok(Self {
            bytes,
            owner: session.owner(),
            budget: b.clone(),
            binding: session.binding().clone(),
            objects,
            graph: native.map(NativeClosure::digest),
            required,
        })
    }
    pub(crate) fn check_owner(&self, session: &Session) -> Result<(), Error> {
        check(&self.budget)?;
        if !self.owner.matches(session)
            || !self.budget.shares_owner(session.budget())
            || session.binding() != &self.binding
        {
            return Err(contract(&self.budget, "native configuration original session"));
        }
        Ok(())
    }
    pub(crate) fn bytes(&self, session: &Session) -> Result<&[u8], Error> {
        self.check_owner(session)?;
        if session.phase() != Phase::AwaitReady {
            return Err(contract(&self.budget, "native configuration original session"));
        }
        Ok(&self.bytes)
    }
}
fn append(out: &mut Vec<u8>, bytes: &[u8], b: &Budget) -> Result<(), Error> {
    if out.len().checked_add(bytes.len()).is_none_or(|n| n > MAX) {
        return Err(contract(b, "native configuration byte bound"));
    }
    charge(b, Charge { work: bytes.len() as u64, ..Charge::default() })?;
    out.extend_from_slice(bytes);
    Ok(())
}
fn field(out: &mut Vec<u8>, bytes: &[u8], b: &Budget) -> Result<(), Error> {
    let n =
        u16::try_from(bytes.len()).map_err(|_| contract(b, "native configuration field bound"))?;
    append(out, &n.to_le_bytes(), b)?;
    append(out, bytes, b)
}

pub(super) struct Decoded {
    pub binding: Binding,
    pub graph: Option<[u8; 32]>,
    pub root: Option<usize>,
    pub objects: Vec<NativeObjectReceipt>,
    pub inputs: Vec<PinnedInput>,
    files: Vec<File>,
    max: u64,
}
impl Decoded {
    pub fn receive(binding: Binding, b: &Budget) -> Result<Self, Error> {
        let mut prefix = [0; 4];
        io::read_exact(&mut prefix, b)?;
        let length = u32::from_le_bytes(prefix) as usize;
        if length == 0 || length > MAX {
            return Err(contract(b, "native configuration length"));
        }
        charge(
            b,
            Charge { wire_bytes: (length + 4) as u64, work: length as u64, ..Charge::default() },
        )?;
        let mut bytes = reserve(length, b)?;
        bytes.resize(length, 0);
        io::read_exact(&mut bytes, b)?;
        Self::decode(&bytes, binding, b)
    }
    fn decode(bytes: &[u8], binding: Binding, b: &Budget) -> Result<Self, Error> {
        let mut read = Reader { bytes, at: 0, budget: b };
        if read.take(8)? != b"NCFGv001" {
            return Err(contract(b, "native configuration version"));
        }
        let worker_size = read.u64()?;
        let max = read.u64()?;
        let graph: [u8; 32] = read.take(32)?.try_into().unwrap();
        let count = read.byte()? as usize;
        if max == 0
            || max == u64::MAX
            || worker_size == 0
            || count > OBJECTS
            || (count == 0) != (graph == [0; 32])
        {
            return Err(contract(b, "native configuration shape"));
        }
        let mut objects = reserve(count, b)?;
        let mut root = None;
        for at in 0..count {
            let sha256 = read.take(32)?.try_into().unwrap();
            let size = read.u64()?;
            let role = match read.byte()? {
                0 => {
                    if root.replace(at).is_some() {
                        return Err(contract(b, "native multiple roots"));
                    }
                    NativeRole::Macro
                }
                1 => NativeRole::Runtime,
                2 => NativeRole::Dependency,
                _ => return Err(contract(b, "native configuration role")),
            };
            let soname = read.field(NAME)?;
            let needed = read.list(OBJECTS, NAME)?;
            let aliases = read.list(ALIASES, PATH)?;
            objects.push(NativeObjectReceipt {
                input: InputIdentity { sha256, size, executable: true },
                role,
                soname,
                needed,
                aliases,
            });
        }
        if read.at != bytes.len() || count != 0 && root.is_none() {
            return Err(contract(b, "native configuration trailing/missing root"));
        }
        let mut files = reserve(count, b)?;
        let mut inputs = reserve(count, b)?;
        for (at, object) in objects.iter().enumerate() {
            let fd = (5 + at) as i32;
            // SAFETY: observations before taking unique ownership of the
            // dense B3 input. Fresh trusted entry has no other FD owner here.
            let (valid, flags, seals) = unsafe {
                (
                    libc::fcntl(fd, libc::F_GETFD),
                    libc::fcntl(fd, libc::F_GETFL),
                    libc::fcntl(fd, libc::F_GET_SEALS),
                )
            };
            let required =
                libc::F_SEAL_WRITE | libc::F_SEAL_GROW | libc::F_SEAL_SHRINK | libc::F_SEAL_SEAL;
            if valid < 0
                || flags < 0
                || flags & libc::O_ACCMODE != libc::O_RDONLY
                || seals < 0
                || seals & required != required
            {
                return Err(contract(b, "native bootstrap dense immutable input"));
            }
            // SAFETY: successful checks confirm the live uniquely inherited
            // source; no other trusted startup File wraps this dense role.
            files.push(unsafe { File::from_raw_fd(fd) });
            inputs.push(PinnedInput {
                fd,
                sha256: object.input.sha256,
                size: object.input.size,
                executable: false,
            });
        }
        let result = Self {
            binding,
            graph: (graph != [0; 32]).then_some(graph),
            root,
            objects,
            inputs,
            files,
            max,
        };
        // The executable was already sealed/hash-admitted by the parent. This
        // handle names that same exec object; it drops before confinement.
        let executable = File::open("/proc/self/exe")
            .map_err(|error| Error::System("native own executable", error))?;
        if executable
            .metadata()
            .map_err(|error| Error::System("native own executable size", error))?
            .len()
            != worker_size
        {
            return Err(contract(b, "native worker size identity"));
        }
        let worker = InputSource {
            file: &executable,
            sha256: result.binding.worker,
            size: worker_size,
            executable: true,
        };
        let mut static_inputs = reserve(count, b)?;
        for (file, object) in result.files.iter().zip(&result.objects) {
            static_inputs.push(InputSource {
                file,
                sha256: object.input.sha256,
                size: object.input.size,
                executable: false,
            });
        }
        let identity = InputClosureIdentity::from_plan(&worker, &static_inputs, result.graph)?;
        if identity.digest() != result.binding.input_closure {
            return Err(contract(b, "native bootstrap composite identity"));
        }
        if let Some(root) = result.root {
            if result.objects[root].input.sha256 != result.binding.artifact {
                return Err(contract(b, "native bootstrap root artifact"));
            }
            result.with_plans(b, |plans| {
                if Some(digest(plans, max, b)?) != result.graph {
                    return Err(contract(b, "native bootstrap graph digest"));
                }
                Ok(())
            })?;
        }
        check(b)?;
        Ok(result)
    }
    pub fn inventory(&self, b: &Budget) -> Result<Inventory, Error> {
        let graph = self.graph.ok_or_else(|| contract(b, "native broker requires graph"))?;
        self.with_plans(b, |plans| Inventory::prepare_delegated(plans, graph, self.max, b))
    }
    pub fn root_alias(&self, b: &Budget) -> Result<Vec<u8>, Error> {
        let root = self.root.ok_or_else(|| contract(b, "native worker requires root"))?;
        let alias =
            self.objects[root].aliases.first().ok_or_else(|| contract(b, "native root alias"))?;
        let mut result = reserve(alias.len() + 1, b)?;
        result.extend_from_slice(alias);
        result.push(0);
        Ok(result)
    }
    fn with_plans<T>(
        &self,
        b: &Budget,
        visit: impl FnOnce(&[NativeObjectPlan<'_>]) -> Result<T, Error>,
    ) -> Result<T, Error> {
        let mut needed = reserve(self.objects.len(), b)?;
        let mut aliases = reserve(self.objects.len(), b)?;
        for object in &self.objects {
            let mut ns = reserve(object.needed.len(), b)?;
            for value in &object.needed {
                ns.push(
                    std::str::from_utf8(value)
                        .map_err(|_| contract(b, "native needed encoding"))?,
                );
            }
            needed.push(ns);
            let mut ns = reserve(object.aliases.len(), b)?;
            for value in &object.aliases {
                ns.push(
                    std::str::from_utf8(value).map_err(|_| contract(b, "native alias encoding"))?,
                );
            }
            aliases.push(ns);
        }
        let mut plans = reserve(self.objects.len(), b)?;
        for (at, object) in self.objects.iter().enumerate() {
            plans.push(NativeObjectPlan {
                source: InputSource {
                    file: &self.files[at],
                    sha256: object.input.sha256,
                    size: object.input.size,
                    executable: true,
                },
                role: object.role,
                soname: std::str::from_utf8(&object.soname)
                    .map_err(|_| contract(b, "native SONAME encoding"))?,
                needed: &needed[at],
                aliases: &aliases[at],
            });
        }
        visit(&plans)
    }
}
struct Reader<'a> {
    bytes: &'a [u8],
    at: usize,
    budget: &'a Budget,
}
impl<'a> Reader<'a> {
    fn take(&mut self, n: usize) -> Result<&'a [u8], Error> {
        charge(self.budget, Charge { work: n as u64, ..Charge::default() })?;
        let end =
            self.at.checked_add(n).ok_or_else(|| contract(self.budget, "native field overflow"))?;
        let value = self
            .bytes
            .get(self.at..end)
            .ok_or_else(|| contract(self.budget, "native field truncation"))?;
        self.at = end;
        Ok(value)
    }
    fn byte(&mut self) -> Result<u8, Error> {
        Ok(self.take(1)?[0])
    }
    fn u64(&mut self) -> Result<u64, Error> {
        Ok(u64::from_le_bytes(self.take(8)?.try_into().unwrap()))
    }
    fn field(&mut self, max: usize) -> Result<Vec<u8>, Error> {
        let n = u16::from_le_bytes(self.take(2)?.try_into().unwrap()) as usize;
        if n == 0 || n > max {
            return Err(contract(self.budget, "native field length"));
        }
        let value = self.take(n)?;
        let mut owned = reserve(n, self.budget)?;
        owned.extend_from_slice(value);
        Ok(owned)
    }
    fn list(&mut self, max: usize, width: usize) -> Result<Vec<Vec<u8>>, Error> {
        let n = self.byte()? as usize;
        if n > max {
            return Err(contract(self.budget, "native list length"));
        }
        let mut result = reserve(n, self.budget)?;
        for _ in 0..n {
            result.push(self.field(width)?);
        }
        Ok(result)
    }
}
pub(super) fn begin(b: &Budget) -> Result<Envelope, Error> {
    let mut prefix = [0; 4];
    io::read_exact(&mut prefix, b)?;
    let length = trust_process_isolation::frame_payload_length(prefix, b).map_err(Error::Budget)?;
    let mut bytes = reserve(length + 4, b)?;
    charge(b, Charge { work: (length + 4) as u64, ..Charge::default() })?;
    bytes.resize(length + 4, 0);
    bytes[..4].copy_from_slice(&prefix);
    io::read_exact(&mut bytes[4..], b)?;
    let begin = trust_process_isolation::decode(&bytes, b).map_err(Error::Budget)?;
    if !matches!(begin.message, Message::Begin { .. }) {
        return Err(contract(b, "native bootstrap Begin"));
    }
    Ok(begin)
}
