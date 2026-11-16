use std::fs::{File, OpenOptions};
use std::io::Write;
use std::path::PathBuf;
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{Duration, Instant};

use sha2::{Digest, Sha256};
use trust_process_isolation::{Binding, Budget, Limits, Session};

use super::admission::{ARCH, Admission, Data, Memory, Notification};
use super::{NativeClosure, NativeObjectPlan, NativeRole, digest};
use crate::launcher::{InputClosureIdentity, InputSource};

mod kernel;

static SEQUENCE: AtomicU64 = AtomicU64::new(0);
struct Source {
    file: File,
    path: PathBuf,
    bytes: Vec<u8>,
}
impl Source {
    fn new(bytes: Vec<u8>) -> Self {
        let path = std::env::temp_dir().join(format!(
            "trust-native-source-{}-{}",
            std::process::id(),
            SEQUENCE.fetch_add(1, Ordering::Relaxed)
        ));
        let mut file =
            OpenOptions::new().create_new(true).read(true).write(true).open(&path).unwrap();
        file.write_all(&bytes).unwrap();
        Self { file, path, bytes }
    }
    fn plan(&self) -> NativeObjectPlan<'_> {
        NativeObjectPlan {
            source: InputSource {
                file: &self.file,
                sha256: Sha256::digest(&self.bytes).into(),
                size: self.bytes.len() as u64,
                executable: true,
            },
            role: NativeRole::Macro,
            soname: "libfixture.so",
            needed: &[],
            aliases: &["/trust-cap/libfixture.so", "/frozen-alias/libfixture.so"],
        }
    }
}
impl Drop for Source {
    fn drop(&mut self) {
        let _ = std::fs::remove_file(&self.path);
    }
}
pub(super) fn budget() -> Budget {
    bounded(u64::MAX / 2, u64::MAX / 2)
}
fn bounded(work: u64, allocation: u64) -> Budget {
    Budget::new(
        Limits {
            frame_bytes: 8192,
            wire_bytes: 1 << 20,
            allocation_bytes: allocation,
            values: 10000,
            work,
            calls: 10000,
            live_handles: 100,
            depth: 32,
        },
        Instant::now() + Duration::from_secs(30),
    )
    .unwrap()
}
fn binding(plans: &[NativeObjectPlan<'_>]) -> Binding {
    Binding {
        version: 1,
        invocation: 7,
        compiler: [1; 32],
        worker: [2; 32],
        artifact: plans[0].source.sha256,
        metadata: [3; 32],
        unit: [4; 32],
        input_closure: identity(plans).digest(),
        host_abi: [5; 32],
    }
}
fn identity(plans: &[NativeObjectPlan<'_>]) -> InputClosureIdentity {
    // Native-only fixtures declare a static component; B3 separately verifies
    // actual ET_EXEC bytes when the two preparations are joined.
    let worker =
        InputSource { file: plans[0].source.file, sha256: [2; 32], size: 1, executable: true };
    InputClosureIdentity::from_plan(&worker, &[], Some(digest(plans, 1 << 20, &budget()).unwrap()))
        .unwrap()
}
fn prepare(
    plans: &[NativeObjectPlan<'_>],
    binding: Binding,
    max: u64,
    budget: Budget,
) -> Result<NativeClosure, crate::Error> {
    let session = Session::new(binding, budget).map_err(crate::Error::Budget)?;
    NativeClosure::prepare(plans, identity(plans), &session, max)
}
pub(super) fn closure(b: Budget) -> NativeClosure {
    let source = Source::new(elf());
    let plans = [source.plan()];
    prepare(&plans, binding(&plans), 1 << 20, b).unwrap()
}
/// Synthetic structural codec context only. The declared worker has no
/// executable provenance and is never launched by receipt parser tests.
pub(super) fn receipt_configuration() -> (Session, super::configuration::Configuration) {
    let b = budget();
    let source = Source::new(elf());
    let plans = [source.plan()];
    let worker = InputSource { file: &source.file, sha256: [2; 32], size: 1, executable: true };
    let data = InputSource { executable: false, ..plans[0].source };
    let identity = InputClosureIdentity::from_plan(
        &worker,
        &[data],
        Some(digest(&plans, 1 << 20, &b).unwrap()),
    )
    .unwrap();
    let mut binding = binding(&plans);
    binding.input_closure = identity.digest();
    let session = Session::new(binding, b).unwrap();
    let native = NativeClosure::prepare(&plans, identity, &session, 1 << 20).unwrap();
    let config = super::configuration::Configuration::prepare(
        crate::launcher::InputIdentity {
            sha256: worker.sha256,
            size: worker.size,
            executable: true,
        },
        1 << 20,
        Some(&native),
        &session,
    )
    .unwrap();
    (session, config)
}
fn elf() -> Vec<u8> {
    let mut bytes = vec![0; 8192];
    bytes[..7].copy_from_slice(b"\x7fELF\x02\x01\x01");
    set16(&mut bytes, 16, 3);
    #[cfg(target_arch = "aarch64")]
    set16(&mut bytes, 18, 183);
    #[cfg(target_arch = "x86_64")]
    set16(&mut bytes, 18, 62);
    set32(&mut bytes, 20, 1);
    set64(&mut bytes, 32, 64);
    set16(&mut bytes, 52, 64);
    set16(&mut bytes, 54, 56);
    set16(&mut bytes, 56, 4);
    program(&mut bytes, 64, 1, 5, 0, 0, 4096, 4096);
    program(&mut bytes, 120, 1, 6, 4096, 4096, 4096, 4096);
    program(&mut bytes, 176, 2, 6, 0x1100, 0x1100, 64, 64);
    program(&mut bytes, 232, 0x6474e551, 6, 0, 0, 0, 0);
    set64(&mut bytes, 0x1100, 5);
    set64(&mut bytes, 0x1108, 0x1800);
    set64(&mut bytes, 0x1110, 10);
    set64(&mut bytes, 0x1118, 32);
    set64(&mut bytes, 0x1120, 14);
    set64(&mut bytes, 0x1128, 1);
    bytes[0x1801..0x180e].copy_from_slice(b"libfixture.so");
    bytes
}
fn set16(b: &mut [u8], n: usize, v: u16) {
    b[n..n + 2].copy_from_slice(&v.to_le_bytes());
}
fn set32(b: &mut [u8], n: usize, v: u32) {
    b[n..n + 4].copy_from_slice(&v.to_le_bytes());
}
fn set64(b: &mut [u8], n: usize, v: u64) {
    b[n..n + 8].copy_from_slice(&v.to_le_bytes());
}
fn program(
    b: &mut [u8],
    at: usize,
    kind: u32,
    flags: u32,
    off: u64,
    addr: u64,
    files: u64,
    mem: u64,
) {
    set32(b, at, kind);
    set32(b, at + 4, flags);
    set64(b, at + 8, off);
    set64(b, at + 16, addr);
    set64(b, at + 32, files);
    set64(b, at + 40, mem);
    set64(b, at + 48, 4096);
}
struct Bytes {
    path: Vec<u8>,
    how: [u8; 24],
    copies: usize,
}
impl Bytes {
    fn good() -> Self {
        Self { path: b"/trust-cap/libfixture.so\0".to_vec(), how: [0; 24], copies: 0 }
    }
}
impl Memory for Bytes {
    fn copy(&mut self, _: u64, address: u64, dst: &mut [u8]) -> Result<usize, crate::Error> {
        self.copies += 1;
        let (source, start) = if (4096..8192).contains(&address) {
            (&self.path[..], (address - 4096) as usize)
        } else if (8192..8216).contains(&address) {
            (&self.how[..], (address - 8192) as usize)
        } else {
            return Err(crate::Error::Contract("fixture unmapped"));
        };
        if start >= source.len() {
            return Ok(0);
        }
        let n = dst.len().min(source.len() - start);
        dst[..n].copy_from_slice(&source[start..start + n]);
        Ok(n)
    }
}
fn notification() -> Notification {
    Notification {
        id: 9,
        pid: 77,
        flags: 0,
        data: Data {
            nr: libc::SYS_openat as i32,
            arch: ARCH,
            ip: 0,
            args: [libc::AT_FDCWD as i64 as u64, 4096, libc::O_CLOEXEC as u64, 0, 0, 0],
        },
    }
}
fn admission() -> Admission {
    let mut a = Admission::new(closure(budget()));
    a.activate(77).unwrap();
    a
}

#[test]
fn closure_is_binding_exact_and_immutable_after_source_move() {
    let source = Source::new(elf());
    let plans = [source.plan()];
    let bind = binding(&plans);
    let b = budget();
    let closure = prepare(&plans, bind.clone(), 1 << 20, b.clone()).unwrap();
    assert_eq!(closure.binding().input_closure, bind.input_closure);
    assert_eq!(closure.digest(), digest(&plans, 1 << 20, &budget()).unwrap());
    assert_eq!(closure.object_count(), 1);
    assert_eq!(closure.objects[0].soname, b"libfixture.so");
    assert!(closure.objects[0].needed.is_empty());
    let moved = source.path.with_extension("moved");
    std::fs::rename(&source.path, &moved).unwrap();
    std::fs::write(&moved, b"overwritten").unwrap();
    std::fs::remove_file(&moved).unwrap();
    let s = &closure.objects[0].snapshot;
    let first = crate::launcher::snapshot::fresh_readonly(s, &b).unwrap();
    let second = crate::launcher::snapshot::fresh_readonly(s, &b).unwrap();
    use std::io::Read;
    let mut a = &first;
    let mut c = &second;
    let mut aa = [0; 4];
    let mut cc = [0; 4];
    a.read_exact(&mut aa).unwrap();
    c.read_exact(&mut cc).unwrap();
    assert_eq!(aa, b"\x7fELF"[..]);
    assert_eq!(aa, cc);
    let receipt = closure.into_receipt();
    assert_eq!(receipt.identity.digest(), bind.input_closure);
    assert_eq!(receipt.graph_digest, digest(&plans, 1 << 20, &budget()).unwrap());
    assert_eq!(receipt.input_bytes, source.bytes.len() as u64);
    assert_eq!(receipt.objects.len(), 1);
    let expected: [u8; 32] = Sha256::digest(&source.bytes).into();
    assert_eq!(receipt.objects[0].input.sha256, expected);
    assert_eq!(receipt.objects[0].role, NativeRole::Macro);
    assert_eq!(receipt.objects[0].soname, b"libfixture.so");
    assert_eq!(
        receipt.objects[0].aliases,
        [b"/trust-cap/libfixture.so".to_vec(), b"/frozen-alias/libfixture.so".to_vec()]
    );
}

#[test]
fn native_graph_requires_its_component_in_the_composite_identity() {
    let source = Source::new(elf());
    let plans = [source.plan()];
    let worker = InputSource { sha256: [2; 32], size: 1, ..plans[0].source };
    for native in [None, Some([9; 32])] {
        let identity = InputClosureIdentity::from_plan(&worker, &[], native).unwrap();
        let mut binding = binding(&plans);
        binding.input_closure = identity.digest();
        let b = budget();
        let session = Session::new(binding, b.clone()).unwrap();
        assert!(NativeClosure::prepare(&plans, identity, &session, 1 << 20).is_err());
        assert!(b.check().is_err());
    }
}

#[test]
fn native_join_rejects_reconstructed_sessions_static_substitution_and_advanced_phase() {
    enum Mismatch {
        Owner,
        StaticInputs,
        Advanced,
    }
    for mismatch in [Mismatch::Owner, Mismatch::StaticInputs, Mismatch::Advanced] {
        let source = Source::new(elf());
        let plans = [source.plan()];
        let identity = identity(&plans);
        let b = budget();
        let mut session = Session::new(binding(&plans), b.clone()).unwrap();
        let native = NativeClosure::prepare(&plans, identity, &session, 1 << 20).unwrap();
        let result = match mismatch {
            Mismatch::Owner => {
                let reconstructed = Session::new(session.binding().clone(), b.clone()).unwrap();
                native.check_invocation(&identity, &reconstructed)
            }
            Mismatch::StaticInputs => {
                let worker = InputSource { sha256: [8; 32], size: 1, ..plans[0].source };
                let changed =
                    InputClosureIdentity::from_plan(&worker, &[], Some(native.digest())).unwrap();
                native.check_invocation(&changed, &session)
            }
            Mismatch::Advanced => {
                session
                    .receive(trust_process_isolation::Envelope {
                        binding: session.binding().clone(),
                        message: trust_process_isolation::Message::Ready,
                    })
                    .unwrap();
                native.check_invocation(&identity, &session)
            }
        };
        assert!(result.is_err());
        assert_eq!(b.check(), Err(trust_process_isolation::Error::Identity));
    }
}
#[test]
fn closure_exact_and_one_short_grants_cannot_reset() {
    let source = Source::new(elf());
    let plans = [source.plan()];
    let bind = binding(&plans);
    let b = budget();
    prepare(&plans, bind.clone(), 1 << 20, b.clone()).unwrap();
    let usage = b.usage().unwrap();
    prepare(&plans, bind.clone(), 1 << 20, bounded(usage.work, usage.allocation_bytes)).unwrap();
    for (work, allocation) in
        [(usage.work - 1, usage.allocation_bytes), (usage.work, usage.allocation_bytes - 1)]
    {
        let b = bounded(work, allocation);
        let peer = b.clone();
        assert!(prepare(&plans, bind.clone(), 1 << 20, b).is_err());
        assert!(peer.check().is_err());
    }
    let mut bad = bind;
    bad.artifact = [8; 32];
    let b = budget();
    assert!(prepare(&plans, bad, 1 << 20, b.clone()).is_err());
    assert!(b.check().is_err());
}
#[test]
fn plan_bounds_graph_roles_and_alias_ambiguity_refuse_before_copy() {
    let source = Source::new(elf());
    let p = source.plan();
    for plan in [
        NativeObjectPlan { role: NativeRole::Runtime, ..p },
        NativeObjectPlan { needed: &["missing.so"], ..p },
        NativeObjectPlan { aliases: &["/a/../b"], ..p },
        NativeObjectPlan { aliases: &["/same", "/same"], ..p },
    ] {
        let b = budget();
        assert!(digest(&[plan], 1 << 20, &b).is_err());
        assert!(b.check().is_err());
        assert_eq!(b.usage().unwrap().allocation_bytes, 0);
    }
    let b = budget();
    assert!(digest(&[p, p], 1 << 20, &b).is_err());
    assert!(b.check().is_err());
}
#[test]
fn elf_native_domain_dynamic_tags_and_ranges_are_checked() {
    let original = elf();
    for edit in 0..12 {
        let mut bytes = original.clone();
        match edit {
            0 => bytes[0] = 0,
            1 => set16(&mut bytes, 16, 2),
            2 => set16(&mut bytes, 18, 0),
            3 => set32(&mut bytes, 68, 7),
            4 => set64(&mut bytes, 128, 4097),
            5 => set32(&mut bytes, 176, 3),
            6 => set32(&mut bytes, 236, 7),
            7 => set64(&mut bytes, 0x1120, 0x7fffffff),
            8 => set64(&mut bytes, 0x1118, u64::MAX),
            9 => set64(&mut bytes, 0x1128, 31),
            10 => set64(&mut bytes, 0x1130, 1),
            _ => set64(&mut bytes, 0x1108, u64::MAX),
        }
        let source = Source::new(bytes);
        let plans = [source.plan()];
        let b = budget();
        assert!(prepare(&plans, binding(&plans), 1 << 20, b.clone()).is_err(), "edit{edit}");
        assert!(b.check().is_err());
    }
}
#[test]
fn notification_identity_directory_flags_and_unknown_aliases_are_terminal() {
    for edit in 0..15 {
        let mut a = admission();
        let b = a.closure.budget.clone();
        let mut n = notification();
        let mut mem = Bytes::good();
        match edit {
            0 => n.pid += 1,
            1 => n.flags = 1,
            2 => n.data.arch ^= 1,
            3 => n.id = 0,
            4 => n.data.nr = libc::SYS_write as i32,
            5 => n.data.args[0] = 3,
            6 => n.data.args[2] = libc::O_WRONLY as u64,
            7 => n.data.args[2] = libc::O_PATH as u64,
            8 => n.data.args[2] |= 1 << 63,
            9 => n.data.args[3] = 1,
            10 => mem.path = b"/proc/self/fd/1\0".to_vec(),
            11 => mem.path = b"relative\0".to_vec(),
            12 => n.data.args[1] = u64::MAX - 1,
            13 => n.data.args[0] = (1 << 32) | libc::AT_FDCWD as u32 as u64,
            _ => n.data.args[3] = 1 << 32,
        }
        assert!(a.admit(n, &mut mem).is_err(), "edit{edit}");
        assert!(b.check().is_err());
        assert!(a.activate(77).is_err());
    }
}
#[test]
fn native_bank_is_one_shot_and_atomic_phase_cannot_replay() {
    let mut a = admission();
    let mut mem = Bytes::good();
    for fd in 33..=63 {
        let grant = a.admit(notification(), &mut mem).unwrap();
        assert_eq!(grant.target, fd);
        a.commit(grant, fd).unwrap();
    }
    assert!(a.admit(notification(), &mut mem).is_err());
    assert!(a.closure.budget.check().is_err());
    let mut a = admission();
    let grant = a.admit(notification(), &mut mem).unwrap();
    assert!(a.commit(grant, 34).is_err());
    assert!(a.closure.budget.check().is_err());
    let mut a = admission();
    a.admit(notification(), &mut mem).unwrap();
    assert!(a.admit(notification(), &mut mem).is_err());
}
#[test]
fn openat2_layout_pointer_and_no_nul_bounds_refuse() {
    let mut a = admission();
    let mut n = notification();
    let mut m = Bytes::good();
    n.data.nr = libc::SYS_openat2 as i32;
    n.data.args[2] = 8192;
    n.data.args[3] = 24;
    let g = a.admit(n, &mut m).unwrap();
    a.commit(g, 33).unwrap();
    for edit in 0..4 {
        let mut a = admission();
        let mut bad = n;
        let mut m = Bytes::good();
        match edit {
            0 => bad.data.args[3] = 25,
            1 => m.how[16] = 1,
            2 => m.how[8] = 1,
            _ => bad.data.args[2] = u64::MAX - 8,
        }
        assert!(a.admit(bad, &mut m).is_err());
        assert!(a.closure.budget.check().is_err());
    }
    let mut a = admission();
    let mut m = Bytes::good();
    m.path = vec![b'/'; 4096];
    assert!(a.admit(notification(), &mut m).is_err());
}
