//! Real sealed-exec/native-entry join. No DSO or production broker is implied.
use std::fs::File;
use std::io::{Read, Write};
use std::os::fd::{AsRawFd, FromRawFd};
use std::time::{Duration, Instant};

use sha2::{Digest, Sha256};
use trust_process_isolation::{
    Binding, Budget, Charge, Envelope, Handle, HandleKind, Limits, Message, Session,
};

use super::{bootstrap, grant, owner, receipt};
use crate::launcher::child::{NativeChannels, spawn_native};
use crate::launcher::{InputClosureIdentity, InputSource, LaunchLimits, PreparedStaticWorker};

static SEQUENCE: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
const OUTPUT: usize = 4096;
const HELPER_LIMITS: Limits = Limits {
    frame_bytes: 8192,
    wire_bytes: 1_000_000,
    allocation_bytes: 4_000_000,
    values: 4096,
    work: 40_000_000,
    calls: 64,
    live_handles: 64,
    depth: 16,
};

struct Output {
    file: File,
    capture: crate::launcher::Capture,
}
struct Outputs {
    worker: Output,
    worker_error: Output,
    broker: Output,
    broker_error: Output,
}
impl Outputs {
    fn tick(&mut self, budget: &Budget) -> Result<(), crate::Error> {
        for output in
            [&mut self.worker, &mut self.worker_error, &mut self.broker, &mut self.broker_error]
        {
            output.capture.read(&mut output.file, OUTPUT, budget)?;
        }
        Ok(())
    }
    fn drain(&mut self, budget: &Budget) -> Result<(), crate::Error> {
        while [&self.worker, &self.worker_error, &self.broker, &self.broker_error]
            .iter()
            .any(|output| !output.capture.closed())
        {
            self.tick(budget)?;
        }
        Ok(())
    }
    fn diagnostics(&mut self) -> [Vec<u8>; 4] {
        [&mut self.worker, &mut self.worker_error, &mut self.broker, &mut self.broker_error].map(
            |stream| {
                let mut bytes = stream.capture.bytes().to_vec();
                if bytes.len() <= OUTPUT {
                    bytes.extend(output(&mut stream.file, OUTPUT + 1 - bytes.len()));
                }
                assert!(bytes.len() <= OUTPUT + 1, "native post-cleanup diagnostic bound");
                bytes
            },
        )
    }
}

struct Scratch(std::path::PathBuf);
impl Drop for Scratch {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir(&self.0);
    }
}
struct Pair {
    owner: owner::Running,
    control: std::os::unix::net::UnixStream,
    standby: std::os::unix::net::UnixStream,
    bootstrap: File,
    broker_bootstrap: File,
    pids: [i32; 2],
    budget: Budget,
    session: Session,
    begin: Envelope,
    configuration: super::Configuration,
    worker_grant: grant::Grant,
    broker_grant: grant::Grant,
    real_broker: bool,
    outputs: Outputs,
    _prepared: PreparedStaticWorker,
    _scratch: Scratch,
}
fn socket() -> (File, File) {
    let mut fds = [-1; 2];
    // SAFETY: two complete writable slots; success returns unique owned FDs.
    assert_eq!(
        unsafe {
            libc::socketpair(
                libc::AF_UNIX,
                libc::SOCK_SEQPACKET | libc::SOCK_CLOEXEC | libc::SOCK_NONBLOCK,
                0,
                fds.as_mut_ptr(),
            )
        },
        0
    );
    // SAFETY: successful socketpair returned two distinct fresh descriptors.
    unsafe { (File::from_raw_fd(fds[0]), File::from_raw_fd(fds[1])) }
}
fn start(mode: &str, duration: Duration) -> Pair {
    start_with_object(mode, duration, None)
}
fn start_with_object(mode: &str, duration: Duration, object: Option<&std::path::Path>) -> Pair {
    let b = Budget::new(
        Limits {
            frame_bytes: 65536,
            wire_bytes: 4_000_000,
            allocation_bytes: 100_000_000,
            values: 10000,
            work: 500_000_000,
            calls: 1000,
            live_handles: 64,
            depth: 16,
        },
        Instant::now() + duration,
    )
    .unwrap();
    let path = std::env::var("TRUST_NATIVE_ENTRY_FIXTURE").expect("actual static fixture required");
    let worker = File::open(&path).unwrap();
    b.charge(Charge {
        allocation_bytes: worker.metadata().unwrap().len(),
        work: 2 * worker.metadata().unwrap().len(),
        ..Charge::default()
    })
    .unwrap();
    let bytes = std::fs::read(path).unwrap();
    let source = InputSource {
        file: &worker,
        sha256: Sha256::digest(&bytes).into(),
        size: bytes.len() as u64,
        executable: true,
    };
    let native_file = object.map(File::open).transpose().unwrap();
    let native_bytes = native_file.as_ref().map(|file| {
        let n = file.metadata().unwrap().len();
        b.charge(Charge { allocation_bytes: n, work: 2 * n, ..Charge::default() }).unwrap();
        std::fs::read(object.unwrap()).unwrap()
    });
    let plans = native_file.as_ref().zip(native_bytes.as_ref()).map(|(file, bytes)| {
        [super::NativeObjectPlan {
            source: InputSource {
                file,
                sha256: Sha256::digest(bytes).into(),
                size: bytes.len() as u64,
                executable: true,
            },
            role: super::NativeRole::Macro,
            soname: "libfixture.so",
            needed: &[],
            aliases: &["/trust-cap/libfixture.so"],
        }]
    });
    let mut inputs = Vec::new();
    if let Some(plans) = &plans {
        inputs.push(InputSource { executable: false, ..plans[0].source });
    }
    let graph = plans.as_ref().map(|plans| super::digest(plans, 32 * 1024 * 1024, &b).unwrap());
    let identity = InputClosureIdentity::from_plan(&source, &inputs, graph).unwrap();
    let session = Session::new(
        Binding {
            version: 1,
            invocation: 1,
            compiler: [1; 32],
            worker: source.sha256,
            artifact: plans.as_ref().map_or([3; 32], |plans| plans[0].source.sha256),
            metadata: [4; 32],
            unit: [5; 32],
            input_closure: identity.digest(),
            host_abi: [7; 32],
        },
        b.clone(),
    )
    .unwrap();
    let limits = LaunchLimits {
        kernel: crate::KernelLimits {
            address_space_bytes: 256 * 1024 * 1024,
            stack_bytes: 8 * 1024 * 1024,
            file_bytes: 1024 * 1024,
            descriptors: if object.is_some() { 1024 } else { 64 },
        },
        sampled_leader_rss_bytes: 256 * 1024 * 1024,
        output_bytes_per_stream: OUTPUT,
        input_bytes: 32 * 1024 * 1024,
    };
    let native = plans.as_ref().map(|plans| {
        super::NativeClosure::prepare(plans, identity, &session, 32 * 1024 * 1024).unwrap()
    });
    let prepared =
        PreparedStaticWorker::prepare(&source, &inputs, native, &session, limits).unwrap();
    let span = Handle {
        invocation: session.binding().invocation,
        slot: 0,
        generation: 1,
        kind: HandleKind::Span,
    };
    let begin = Envelope {
        binding: session.binding().clone(),
        message: Message::Begin {
            declaration: 0,
            kind: 0,
            inputs: vec![Handle {
                invocation: session.binding().invocation,
                slot: 1,
                generation: 1,
                kind: HandleKind::Stream,
            }],
            globals: [span; 3],
        },
    };
    let configuration = prepared.native_configuration(&session, &begin).unwrap();
    let worker_grant = grant::Grant::reserve(&session, grant::Role::Worker, HELPER_LIMITS).unwrap();
    let broker_grant = grant::Grant::reserve(&session, grant::Role::Broker, HELPER_LIMITS).unwrap();
    let [worker_capture, worker_error_capture, broker_capture, broker_error_capture] =
        std::array::from_fn(|_| crate::launcher::Capture::new(OUTPUT, &b).unwrap());
    let path = std::env::temp_dir().join(format!(
        "trust-native-entry-{}-{}",
        std::process::id(),
        SEQUENCE.fetch_add(1, std::sync::atomic::Ordering::Relaxed)
    ));
    std::fs::create_dir(&path).unwrap();
    use std::os::unix::fs::PermissionsExt;
    std::fs::set_permissions(&path, std::fs::Permissions::from_mode(0o700)).unwrap();
    let scratch = Scratch(path);
    let name = std::ffi::CString::new(scratch.0.as_os_str().as_encoded_bytes()).unwrap();
    // SAFETY: owned, terminated scratch path and O_PATH directory role only.
    let raw =
        unsafe { libc::open(name.as_ptr(), libc::O_PATH | libc::O_DIRECTORY | libc::O_CLOEXEC) };
    assert!(raw >= 0);
    // SAFETY: successful open returned a fresh unique descriptor.
    let directory = unsafe { File::from_raw_fd(raw) };
    let owner = owner::Prepared::new(&b).unwrap();
    let (boot, transfer) = socket();
    let (broker_bootstrap, standby_transfer) = socket();
    bootstrap::configure(&boot, &b).unwrap();
    let NativeChannels { child, control, stdout, stderr, status } =
        spawn_native(&prepared, &[mode], directory.as_raw_fd(), transfer.as_raw_fd()).unwrap();
    drop((status, transfer));
    let NativeChannels {
        child: broker,
        control: standby,
        stdout: broker_stdout,
        stderr: broker_stderr,
        status,
    } = spawn_native(
        &prepared,
        &[if object.is_some() { "broker" } else { "standby" }],
        directory.as_raw_fd(),
        standby_transfer.as_raw_fd(),
    )
    .unwrap();
    drop((status, standby_transfer));
    let pids = [child.pid, broker.pid];
    let owner = owner.attach(child, broker);
    loop {
        let seen = owner.observe();
        assert!(seen.grant_valid, "native pair refused before trusted startup: {seen:?}");
        if seen.phase == owner::Phase::Watching {
            break;
        }
        assert_eq!(seen.phase, owner::Phase::Arming);
        std::thread::sleep(Duration::from_millis(1));
    }
    Pair {
        owner,
        control,
        standby,
        bootstrap: boot,
        broker_bootstrap,
        pids,
        budget: b,
        session,
        begin,
        configuration,
        worker_grant,
        broker_grant,
        real_broker: object.is_some(),
        outputs: Outputs {
            worker: Output { file: stdout, capture: worker_capture },
            worker_error: Output { file: stderr, capture: worker_error_capture },
            broker: Output { file: broker_stdout, capture: broker_capture },
            broker_error: Output { file: broker_stderr, capture: broker_error_capture },
        },
        _prepared: prepared,
        _scratch: scratch,
    }
}
fn write(
    stream: &mut std::os::unix::net::UnixStream,
    mut bytes: &[u8],
    b: &Budget,
) -> Result<(), crate::Error> {
    while !bytes.is_empty() {
        b.check().map_err(crate::Error::Budget)?;
        let n = bytes.len().min(4096);
        b.charge(Charge { work: n as u64, ..Charge::default() }).map_err(crate::Error::Budget)?;
        match stream.write(&bytes[..n]) {
            Ok(n) if n > 0 => bytes = &bytes[n..],
            Err(error) if error.kind() == std::io::ErrorKind::WouldBlock => {
                std::thread::sleep(Duration::from_millis(1))
            }
            Err(error) => return Err(crate::Error::System("native parent control write", error)),
            _ => return Err(crate::Error::Contract("native parent control write zero")),
        }
    }
    b.check().map_err(crate::Error::Budget)
}
fn initialize(pair: &mut Pair, broker: bool) -> Result<(), crate::Error> {
    let b = &pair.budget;
    let grant = if broker { &pair.broker_grant } else { &pair.worker_grant };
    let wire = grant.wire(&pair.session)?;
    let config = pair.configuration.bytes(&pair.session)?;
    let begin = trust_process_isolation::encode(&pair.begin, b).map_err(crate::Error::Budget)?;
    b.charge(Charge {
        wire_bytes: (1
            + wire.len()
            + 4
            + config.len()
            + if broker && pair.real_broker { 4 } else { 0 }) as u64,
        ..Charge::default()
    })
    .map_err(crate::Error::Budget)?;
    let control = if broker { &mut pair.standby } else { &mut pair.control };
    write(control, b"C", b)?;
    write(control, wire, b)?;
    write(control, &begin, b)?;
    write(control, &(config.len() as u32).to_le_bytes(), b)?;
    write(control, config, b)?;
    if broker && pair.real_broker {
        write(control, &(pair.pids[0] as u32).to_le_bytes(), b)?;
    }
    Ok(())
}
fn read(stream: &mut std::os::unix::net::UnixStream, bytes: &mut [u8], b: &Budget) {
    read_result(stream, bytes, b).unwrap();
}
fn read_result(
    stream: &mut std::os::unix::net::UnixStream,
    mut bytes: &mut [u8],
    b: &Budget,
) -> Result<(), crate::Error> {
    while !bytes.is_empty() {
        let count = bytes.len().min(4096);
        b.charge(Charge { work: count as u64, ..Charge::default() })
            .map_err(crate::Error::Budget)?;
        match stream.read(&mut bytes[..count]) {
            Ok(0) => return Err(crate::Error::Contract("unexpected native control EOF")),
            Ok(n) => bytes = &mut bytes[n..],
            Err(error) if error.kind() == std::io::ErrorKind::WouldBlock => {
                std::thread::sleep(Duration::from_millis(1));
            }
            Err(error) => return Err(crate::Error::System("native parent control read", error)),
        }
    }
    b.check().map_err(crate::Error::Budget)
}
fn read_active(
    stream: &mut std::os::unix::net::UnixStream,
    mut bytes: &mut [u8],
    b: &Budget,
    outputs: &mut Outputs,
) -> Result<(), crate::Error> {
    while !bytes.is_empty() {
        outputs.tick(b)?;
        let count = bytes.len().min(4096);
        b.charge(Charge { work: count as u64, ..Charge::default() })
            .map_err(crate::Error::Budget)?;
        match stream.read(&mut bytes[..count]) {
            Ok(0) => return Err(crate::Error::Contract("unexpected active native EOF")),
            Ok(n) => bytes = &mut bytes[n..],
            Err(error) if error.kind() == std::io::ErrorKind::WouldBlock => {
                std::thread::sleep(Duration::from_millis(1))
            }
            Err(error) => return Err(crate::Error::System("active native control read", error)),
        }
    }
    outputs.tick(b)?;
    b.check().map_err(crate::Error::Budget)
}
fn listener(pair: &Pair) -> Result<File, crate::Error> {
    loop {
        pair.budget.check().map_err(crate::Error::Budget)?;
        let mut event =
            libc::pollfd { fd: pair.bootstrap.as_raw_fd(), events: libc::POLLIN, revents: 0 };
        // SAFETY: complete fixed poll record and finite original-budget wait.
        let n = unsafe { libc::poll(&mut event, 1, 1) };
        if n < 0 {
            return Err(crate::system("native parent listener poll"));
        }
        if n > 0 {
            if event.revents & libc::POLLIN == 0
                || event.revents & !(libc::POLLIN | libc::POLLHUP) != 0
            {
                return Err(crate::Error::Contract("native parent listener missing/truncated"));
            }
            return bootstrap::receive(&pair.bootstrap, pair.pids[0] as u32, &pair.budget);
        }
    }
}
fn quiescent(pair: &mut Pair) -> u64 {
    let address = addresses(pair);
    initialize(pair, true).unwrap();
    address
}
fn addresses(pair: &mut Pair) -> u64 {
    let mut worker = [0; 8];
    let mut broker = [0; 8];
    read(&mut pair.control, &mut worker, &pair.budget);
    read(&mut pair.standby, &mut broker, &pair.budget);
    assert_ne!(u64::from_le_bytes(worker), 0);
    assert_ne!(u64::from_le_bytes(broker), 0);
    u64::from_le_bytes(worker)
}
fn reaped(pair: &Pair) -> owner::Observation {
    let until = Instant::now() + Duration::from_secs(3);
    loop {
        assert!(Instant::now() < until, "native cleanup pending");
        let seen = pair.owner.observe();
        if seen.phase == owner::Phase::Reaped && seen.monitor_exited {
            return seen;
        }
        assert_ne!(seen.phase, owner::Phase::CleanupFailed);
        std::thread::sleep(Duration::from_millis(1));
    }
}
fn absent(pids: [i32; 2]) {
    for pid in pids {
        let mut status = 0;
        // SAFETY: query only the exact pair already reaped by its monitor.
        assert_eq!(unsafe { libc::waitpid(pid, &mut status, libc::WNOHANG) }, -1);
        assert_eq!(std::io::Error::last_os_error().raw_os_error(), Some(libc::ECHILD));
    }
}

fn frame(
    stream: &mut std::os::unix::net::UnixStream,
    b: &Budget,
    outputs: &mut Outputs,
) -> Result<Envelope, crate::Error> {
    let mut prefix = [0; 4];
    read_active(stream, &mut prefix, b, outputs)?;
    let length =
        trust_process_isolation::frame_payload_length(prefix, b).map_err(crate::Error::Budget)?;
    let mut bytes = super::reserve(length + 4, b)?;
    b.charge(Charge { work: (length + 4) as u64, ..Charge::default() })
        .map_err(crate::Error::Budget)?;
    bytes.resize(length + 4, 0);
    bytes[..4].copy_from_slice(&prefix);
    read_active(stream, &mut bytes[4..], b, outputs)?;
    trust_process_isolation::decode(&bytes, b).map_err(crate::Error::Budget)
}
fn marker(
    stream: &mut std::os::unix::net::UnixStream,
    expected: u8,
    b: &Budget,
    outputs: &mut Outputs,
) -> Result<(), crate::Error> {
    b.charge(Charge { wire_bytes: 1, ..Charge::default() }).map_err(crate::Error::Budget)?;
    let mut byte = [0];
    read_active(stream, &mut byte, b, outputs)?;
    if byte != [expected] {
        return Err(super::contract(b, "native diagnostic phase marker"));
    }
    Ok(())
}
fn command(
    stream: &mut std::os::unix::net::UnixStream,
    byte: u8,
    b: &Budget,
) -> Result<(), crate::Error> {
    b.charge(Charge { wire_bytes: 1, ..Charge::default() }).map_err(crate::Error::Budget)?;
    write(stream, &[byte], b)
}
fn map_receipt(pair: &mut Pair, sequence: u64) -> Result<receipt::Receipt, crate::Error> {
    command(&mut pair.standby, b'M', &pair.budget)?;
    let b = pair.budget.clone();
    receipt::Receipt::receive(
        &pair.session,
        &pair.configuration,
        pair.broker_grant.capsule(),
        sequence,
        |bytes| read_active(&mut pair.standby, bytes, &b, &mut pair.outputs),
    )
}
fn run_load(pair: &mut Pair) -> Result<(receipt::Receipt, receipt::Receipt), crate::Error> {
    run_load_fault(pair, RelayFault::None)
}
#[derive(Clone, Copy)]
enum RelayFault {
    None,
    Capsule,
    MmRoles,
    Task,
}
fn run_load_fault(
    pair: &mut Pair,
    fault: RelayFault,
) -> Result<(receipt::Receipt, receipt::Receipt), crate::Error> {
    addresses(pair);
    let memory = File::open(format!("/proc/{}/mem", pair.pids[0]))
        .map_err(|error| crate::Error::System("owned post-exec mm", error))?;
    let maps = File::open(format!("/proc/{}/maps", pair.pids[0]))
        .map_err(|error| crate::Error::System("owned post-exec maps", error))?;
    initialize(pair, true)?;
    initialize(pair, false)?;
    let listener = listener(pair)?;
    marker(&mut pair.control, b'I', &pair.budget, &mut pair.outputs)?;
    marker(&mut pair.standby, b'A', &pair.budget, &mut pair.outputs)?;
    let mut handoff = bootstrap::BrokerHandoff { listener, memory, maps };
    let mut capsule = pair.broker_grant.capsule();
    let mut task = pair.pids[0] as u32;
    match fault {
        RelayFault::None => {}
        RelayFault::Capsule => capsule[0] ^= 1,
        RelayFault::MmRoles => std::mem::swap(&mut handoff.memory, &mut handoff.maps),
        RelayFault::Task => task = pair.pids[1] as u32,
    }
    bootstrap::send_broker(&pair.broker_bootstrap, task, capsule, &handoff, &pair.budget)?;
    drop(handoff);
    marker(&mut pair.standby, b'B', &pair.budget, &mut pair.outputs)?;
    // No untrusted constructor starts before actual broker confinement/service.
    command(&mut pair.control, b'L', &pair.budget)?;
    marker(&mut pair.control, b'Q', &pair.budget, &mut pair.outputs)?;
    let first = map_receipt(pair, 1)?;
    let mut seen = [false; super::OBJECTS];
    first.validate_progress(None, &pair.configuration, &pair.session, &mut seen)?;
    command(&mut pair.control, b'G', &pair.budget)?;
    let ready = frame(&mut pair.control, &pair.budget, &mut pair.outputs)?;
    if pair.session.receive(ready).map_err(crate::Error::Budget)?
        != trust_process_isolation::Admission::Ready
    {
        return Err(super::contract(&pair.budget, "native diagnostic Ready"));
    }
    pair.configuration.check_owner(&pair.session)?;
    let finish = frame(&mut pair.control, &pair.budget, &mut pair.outputs)?;
    if pair.session.receive(finish).map_err(crate::Error::Budget)?
        != trust_process_isolation::Admission::Finished(None)
    {
        return Err(super::contract(&pair.budget, "native diagnostic Finish"));
    }
    let final_receipt = map_receipt(pair, 2)?;
    final_receipt.validate_progress(Some(&first), &pair.configuration, &pair.session, &mut seen)?;
    pair.owner.request_worker_exit()?;
    while pair.owner.observe().phase != owner::Phase::Finishing {
        pair.budget.check().map_err(crate::Error::Budget)?;
        std::thread::sleep(Duration::from_millis(1));
    }
    command(&mut pair.control, b'E', &pair.budget)?;
    loop {
        pair.outputs.tick(&pair.budget)?;
        pair.budget.check().map_err(crate::Error::Budget)?;
        match pair.control.read(&mut [0]) {
            Ok(0) => break,
            Ok(_) => return Err(super::contract(&pair.budget, "trailing native worker output")),
            Err(error) if error.kind() == std::io::ErrorKind::WouldBlock => {
                std::thread::sleep(Duration::from_millis(1))
            }
            Err(error) => return Err(crate::Error::System("native terminal EOF", error)),
        }
    }
    pair.owner.request_finished()?;
    Ok((first, final_receipt))
}
fn output(file: &mut File, cap: usize) -> Vec<u8> {
    // Bounded post-cleanup diagnostic only, never a grant or verdict. No child
    // can still produce data after the independently observed complete reap.
    let mut bytes = [0; 4097];
    let mut used = 0;
    loop {
        if used == cap {
            return bytes[..used].to_vec();
        }
        match file.read(&mut bytes[used..cap]) {
            Ok(0) => return bytes[..used].to_vec(),
            Ok(n) => used += n,
            Err(error) => panic!("post-reap diagnostic output: {error}"),
        }
    }
}
fn constructor(variant: usize) -> std::path::PathBuf {
    std::path::PathBuf::from(
        std::env::var("TRUST_NATIVE_CONSTRUCTOR_DIR")
            .expect("actual native constructor DSOs required"),
    )
    .join(format!("constructor-{variant}.so"))
}

#[test]
#[ignore = "requires actual static helper and independently compiled native constructor DSOs"]
fn pinned_broker_and_worker_confine_real_constructor_and_bind_mapped_inputs() {
    let mut pair = start_with_object("load", Duration::from_secs(10), Some(&constructor(0)));
    let mut result = run_load(&mut pair);
    if result.is_err() {
        pair.owner.refuse();
    }
    let status = reaped(&pair);
    if result.is_ok() {
        if let Err(error) = pair.outputs.drain(&pair.budget) {
            result = Err(error);
            pair.owner.refuse();
        }
    }
    let [stdout, stderr, broker_stdout, broker_stderr] = pair.outputs.diagnostics();
    assert!(
        result.is_ok(),
        "native load failed: {result:?} status={status:?} stdout={stdout:?} worker_stage={stderr:?} broker_stage={broker_stderr:?}"
    );
    let (first, final_receipt) = result.unwrap();
    assert_eq!((first.sequence, final_receipt.sequence), (1, 2));
    assert_eq!(first.issued.len(), 1);
    assert_eq!(first.issued[0].sha256, pair.session.binding().artifact);
    assert!(!first.observed.is_empty());
    assert!(!final_receipt.observed.is_empty());
    assert_eq!(stdout, [b'K', 7]);
    assert!(stderr.is_empty() && broker_stdout.is_empty() && broker_stderr.is_empty());
    assert_eq!(pair.session.phase(), trust_process_isolation::Phase::Terminal);
    assert_eq!(status.cause, Some(owner::Cause::ParentFinished));
    assert!(libc::WIFEXITED(status.worker_status.unwrap()));
    assert_eq!(libc::WEXITSTATUS(status.worker_status.unwrap()), 0);
    assert_eq!(libc::WTERMSIG(status.broker_status.unwrap()), libc::SIGKILL);
    eprintln!(
        "native OS diagnostic only: issued={:?} mapped_before={:?} mapped_after={:?} status={status:?}",
        first.issued, first.observed, final_receipt.observed
    );
    assert!(pair.owner.finish().unwrap().grant_valid);
    absent(pair.pids);
}

#[test]
#[ignore = "requires actual static helper and independently compiled hostile native constructor DSOs"]
fn hostile_native_constructors_cannot_open_create_exec_write_or_make_code() {
    for variant in 1..=7 {
        let mut pair =
            start_with_object("load", Duration::from_secs(10), Some(&constructor(variant)));
        let result = run_load(&mut pair);
        if result.is_err() {
            pair.owner.refuse();
        }
        let status = reaped(&pair);
        let [stdout, stderr, broker_stdout, broker_stderr] = pair.outputs.diagnostics();
        eprintln!(
            "hostile constructor={variant} result={result:?} status={status:?} worker_stage={stderr:?} broker_stage={broker_stderr:?}"
        );
        assert!(result.is_err(), "hostile constructor{variant} passed");
        assert_eq!(pair.session.phase(), trust_process_isolation::Phase::AwaitReady);
        assert!(stdout.is_empty(), "constructor{variant} reached normal body");
        assert!(broker_stdout.is_empty());
        let worker = status.worker_status.unwrap();
        let broker = status.broker_status.unwrap();
        if variant == 1 {
            assert!(
                libc::WIFEXITED(broker) && libc::WEXITSTATUS(broker) == 138,
                "unknown alias was not refused by actual broker: {status:?}"
            );
        } else {
            assert!(
                libc::WIFSIGNALED(worker) && libc::WTERMSIG(worker) == libc::SIGSYS,
                "authority attempt{variant} was not killed by native filter: {status:?}"
            );
        }
        assert!(!pair.owner.finish().unwrap().grant_valid);
        absent(pair.pids);
    }
}

#[test]
#[ignore = "requires actual static helper and independently compiled native constructor DSOs"]
fn broker_rejects_wrong_capsule_task_and_retained_mm_roles_before_loading() {
    for fault in [RelayFault::Capsule, RelayFault::MmRoles, RelayFault::Task] {
        let mut pair = start_with_object("load", Duration::from_secs(10), Some(&constructor(0)));
        let result = run_load_fault(&mut pair, fault);
        if result.is_err() {
            pair.owner.refuse();
        }
        let status = reaped(&pair);
        let [stdout, _, broker_stdout, broker_stderr] = pair.outputs.diagnostics();
        assert!(result.is_err(), "forged native handoff admitted");
        assert_eq!(pair.session.phase(), trust_process_isolation::Phase::AwaitReady);
        assert!(stdout.is_empty(), "constructor ran before handoff binding");
        assert!(broker_stdout.is_empty());
        assert_eq!(broker_stderr, [132]);
        assert!(libc::WIFEXITED(status.broker_status.unwrap()));
        assert_eq!(libc::WEXITSTATUS(status.broker_status.unwrap()), 132);
        assert!(!pair.owner.finish().unwrap().grant_valid);
        absent(pair.pids);
    }
}

#[test]
#[ignore = "requires actual static helper and independently compiled hostile native constructor DSOs"]
fn native_constructor_output_flood_spends_original_capture_quota_and_reaps() {
    let mut pair = start_with_object("load", Duration::from_secs(10), Some(&constructor(8)));
    let started = Instant::now();
    let result = run_load(&mut pair);
    assert!(
        matches!(result, Err(crate::Error::Contract("output bytes"))),
        "flood escaped original capture quota: {result:?}"
    );
    pair.owner.refuse();
    let status = reaped(&pair);
    assert!(started.elapsed() < Duration::from_secs(10));
    assert_eq!(pair.outputs.worker.capture.bytes().len(), OUTPUT + 1);
    assert_eq!(pair.session.phase(), trust_process_isolation::Phase::AwaitReady);
    assert!(!pair.owner.finish().unwrap().grant_valid);
    absent(pair.pids);
    eprintln!("native flood refused by original capture quota, status={status:?}");
}

#[test]
#[ignore = "requires actual native-entry-fixture static ET_EXEC on Linux"]
fn sealed_exec_native_entry_retains_exact_mm_and_completes_owned_pair() {
    let mut pair = start("entry", Duration::from_secs(10));
    let address = quiescent(&mut pair);
    // These diagnostic reads are not production broker placement. The native
    // executable is still trusted and quiescent before its irreversible entry.
    let memory = File::open(format!("/proc/{}/mem", pair.pids[0])).unwrap();
    let maps = File::open(format!("/proc/{}/maps", pair.pids[0])).unwrap();
    initialize(&mut pair, false).unwrap();
    let listener = loop {
        pair.budget.check().unwrap();
        let mut event =
            libc::pollfd { fd: pair.bootstrap.as_raw_fd(), events: libc::POLLIN, revents: 0 };
        // SAFETY: initialized complete pollfd and finite single-event wait.
        let ready = unsafe { libc::poll(&mut event, 1, 1) };
        assert!(ready >= 0);
        if ready > 0 {
            assert_ne!(event.revents & libc::POLLIN, 0);
            break bootstrap::receive(&pair.bootstrap, pair.pids[0] as u32, &pair.budget).unwrap();
        }
    };
    let mut installed = [0];
    read(&mut pair.control, &mut installed, &pair.budget);
    assert_eq!(&installed, b"I");
    assert!(File::open(format!("/proc/{}/mem", pair.pids[0])).is_err());
    let mut value = [0; 8];
    // SAFETY: exact retained post-exec mm and bounded output at its announced
    // trusted static address. No new child PID path is opened after clamp.
    assert_eq!(
        unsafe {
            libc::pread(memory.as_raw_fd(), value.as_mut_ptr().cast(), value.len(), address as i64)
        },
        8
    );
    assert_eq!(u64::from_le_bytes(value), 456);
    let mut map = [0; 4096];
    // SAFETY: bounded diagnostic observation through retained post-exec maps.
    assert!(unsafe { libc::pread(maps.as_raw_fd(), map.as_mut_ptr().cast(), map.len(), 0) } > 0);
    pair.owner.request_worker_exit().unwrap();
    while pair.owner.observe().phase != owner::Phase::Finishing {
        pair.budget.check().unwrap();
        std::thread::sleep(Duration::from_millis(1));
    }
    pair.owner.request_finished().unwrap();
    pair.control.write_all(b"E").unwrap();
    let seen = reaped(&pair);
    assert_eq!(seen.cause, Some(owner::Cause::ParentFinished));
    assert!(libc::WIFEXITED(seen.worker_status.unwrap()));
    assert_eq!(libc::WEXITSTATUS(seen.worker_status.unwrap()), 0);
    assert_eq!(libc::WTERMSIG(seen.broker_status.unwrap()), libc::SIGKILL);
    drop((memory, maps, listener));
    assert!(pair.owner.finish().unwrap().grant_valid);
    absent(pair.pids);
}

#[test]
#[ignore = "requires actual native-entry-fixture static ET_EXEC on Linux"]
fn sealed_exec_native_entry_rejects_socket_substitution_and_early_exit() {
    for mode in ["bad-transfer", "early-exit"] {
        let mut pair = start(mode, Duration::from_secs(10));
        quiescent(&mut pair);
        initialize(&mut pair, false).unwrap();
        let seen = reaped(&pair);
        assert_eq!(seen.cause, Some(owner::Cause::WorkerExited));
        assert!(!seen.grant_valid);
        assert_eq!(libc::WTERMSIG(seen.broker_status.unwrap()), libc::SIGKILL);
        assert!(!pair.owner.finish().unwrap().grant_valid);
        absent(pair.pids);
    }
}

#[test]
#[ignore = "requires actual native-entry-fixture static ET_EXEC on Linux"]
fn sealed_exec_native_startup_stall_uses_original_deadline_and_reaps_both() {
    let mut pair = start("entry", Duration::from_secs(1));
    addresses(&mut pair);
    // No clamp acknowledgement: neither a loader nor native entry may run.
    let seen = reaped(&pair);
    assert_eq!(seen.cause, Some(owner::Cause::Deadline));
    assert_eq!(libc::WTERMSIG(seen.worker_status.unwrap()), libc::SIGKILL);
    assert_eq!(libc::WTERMSIG(seen.broker_status.unwrap()), libc::SIGKILL);
    assert!(!pair.owner.finish().unwrap().grant_valid);
    absent(pair.pids);
}
