//! Original file-description custody for fixed commands and nested invocations.
//! The packet describes kernel-held files; it grants no GNU, SDK or Host rights.

use std::collections::BTreeSet;
use std::ffi::OsStr;
use std::os::unix::process::CommandExt;
use std::process::{Child, Command, ExitStatus};

use trust_sha2::{Digest, Sha256};

use super::*;

#[path = "handoff/output_member.rs"]
pub(super) mod output_member;
pub use output_member::MemberDirectory;

#[path = "handoff/group.rs"]
mod group;
#[cfg(all(feature = "native-exec", target_os = "macos", target_arch = "aarch64"))]
pub use group::ExecutionStartPipe;
pub use group::{FixedCommandSignal, RunningFixedGroup};

#[cfg(all(feature = "native-exec", target_os = "macos", target_arch = "aarch64"))]
#[path = "handoff/nested.rs"]
mod nested;
#[cfg(all(feature = "native-exec", target_os = "macos", target_arch = "aarch64"))]
pub use nested::{PreparedNestedFixedCommand, RunningNestedFixedCommand};

// Trust: the reader (`read_file`) refuses a packet with any group or other mode
// bit. `tempfile::tempfile()` gives no such file on Linux: there it is an
// `O_TMPFILE` created 0666 less the umask, so 0644 under the usual 022, where the
// macOS path is a 0600 file unlinked after creation. Every handoff was refused
// on Linux as "unsafe fixed handoff packet". Set the mode the reader checks.
fn private_packet() -> io::Result<File> {
    use std::os::unix::fs::PermissionsExt as _;
    let packet = tempfile::tempfile()?;
    packet.set_permissions(fs::Permissions::from_mode(0o600))?;
    Ok(packet)
}

/// Descriptor of the bounded anonymous fixed-claim packet, never a path token.
pub const FIXED_HANDOFF_ENV: &str = "TRUST_FIXED_ADMISSION_FD_V1";

// Keep native inode/time widths while observing every original fstat field.
// These stamps are private equality observations, not a wire representation.
type OriginalDescriptorStamp =
    (u64, libc::ino_t, u64, u32, libc::time_t, libc::c_long, libc::time_t, libc::c_long);

/// Early observations only; this value grants no claim. Snapshot before any
/// descriptor-opening callback, then consume it into the ordinary checked
/// original-description importer. A closed/reused slot cannot be repaired by
/// later startup allocations.
pub struct EarlyFixedClaim {
    descriptor: OsString,
    packet: Vec<u8>,
    originals: Vec<(i32, OriginalDescriptorStamp)>,
}

impl EarlyFixedClaim {
    pub fn snapshot(descriptor: &OsStr) -> io::Result<Self> {
        let fd = descriptor
            .to_str()
            .and_then(|text| text.parse::<i32>().ok())
            .filter(|fd| *fd >= 3)
            .ok_or_else(|| invalid("invalid early fixed packet descriptor"))?;
        let original = Self::observe(fd)?;
        if original.2 > MAX_PACKET {
            return Err(invalid("early fixed packet exceeds bound"));
        }
        let mut packet = vec![0; original.2 as usize];
        Self::read_original(fd, &mut packet)?;
        let (decoded, output) = decode_packet(&packet)?;
        if decoded.files.is_empty() || decoded.files.len() > MAX_TICKETS + 2 {
            return Err(invalid("early fixed original census exceeds bound"));
        }
        if original.3 & libc::S_IFMT as u32 != libc::S_IFREG as u32 {
            return Err(invalid("early fixed packet is not regular"));
        }
        let mut originals = vec![(fd, original)];
        let mut descriptors = BTreeSet::from([fd]);
        for entry in decoded.files {
            if entry.descriptor < 3 || !descriptors.insert(entry.descriptor) {
                return Err(invalid("early fixed descriptor aliases another original"));
            }
            let observed = Self::observe(entry.descriptor)?;
            if observed.3 & libc::S_IFMT as u32 != libc::S_IFREG as u32 {
                return Err(invalid("early fixed claim original is not regular"));
            }
            originals.push((entry.descriptor, observed));
        }
        if let Some(output) = output {
            for (index, fd) in output.descriptors().into_iter().enumerate() {
                if fd < 3 || !descriptors.insert(fd) {
                    return Err(invalid("early output member aliases another original"));
                }
                let observed = Self::observe(fd)?;
                let expected = if index == 0 { libc::S_IFDIR } else { libc::S_IFREG };
                if observed.3 & libc::S_IFMT as u32 != expected as u32 {
                    return Err(invalid("early output member original has the wrong kind"));
                }
                originals.push((fd, observed));
            }
        }
        let captured = Self { descriptor: descriptor.to_owned(), packet, originals };
        captured.check()?;
        Ok(captured)
    }

    fn observe(fd: i32) -> io::Result<OriginalDescriptorStamp> {
        let mut observed = std::mem::MaybeUninit::<libc::stat>::uninit();
        // SAFETY: writable stat, borrowed original descriptor; no allocation,
        // ownership conversion, cursor change, close or lock operation.
        if unsafe { libc::fstat(fd, observed.as_mut_ptr()) } != 0 {
            return Err(io::Error::last_os_error());
        }
        // SAFETY: successful fstat initialized the complete stat value.
        let meta = unsafe { observed.assume_init() };
        if !matches!(meta.st_mode & libc::S_IFMT, libc::S_IFREG | libc::S_IFDIR) || meta.st_size < 0
        {
            return Err(invalid("early fixed original has an unsupported kind"));
        }
        let directory = meta.st_mode & libc::S_IFMT == libc::S_IFDIR;
        Ok((
            meta.st_dev as u64,
            meta.st_ino,
            // Output membership pins directory identity and ownership, not
            // its deliberately mutable child population. V1 regular-file
            // packet/record byte stamps remain unchanged.
            if directory { 0 } else { meta.st_size as u64 },
            meta.st_mode as u32,
            if directory { 0 } else { meta.st_mtime },
            if directory { 0 } else { meta.st_mtime_nsec },
            if directory { 0 } else { meta.st_ctime },
            if directory { 0 } else { meta.st_ctime_nsec },
        ))
    }

    fn read_original(fd: i32, mut bytes: &mut [u8]) -> io::Result<()> {
        let mut offset = 0;
        while !bytes.is_empty() {
            // SAFETY: writable bounded slice; pread observes the borrowed
            // original without changing the shared open-description offset.
            let count = unsafe { libc::pread(fd, bytes.as_mut_ptr().cast(), bytes.len(), offset) };
            if count < 0 {
                let error = io::Error::last_os_error();
                if error.kind() == io::ErrorKind::Interrupted {
                    continue;
                }
                return Err(error);
            }
            if count == 0 {
                return Err(io::ErrorKind::UnexpectedEof.into());
            }
            offset += count as libc::off_t;
            bytes = &mut bytes[count as usize..];
        }
        Ok(())
    }

    fn check(&self) -> io::Result<()> {
        for (fd, expected) in &self.originals {
            if Self::observe(*fd)? != *expected {
                return Err(invalid("early fixed original descriptor changed"));
            }
        }
        let fd = self.originals[0].0;
        let mut current = vec![0; self.packet.len()];
        Self::read_original(fd, &mut current)?;
        if current != self.packet {
            return Err(invalid("early fixed original packet changed"));
        }
        Ok(())
    }

    pub fn capture(self) -> io::Result<InheritedFixedClaim> {
        self.check()?;
        let original = InheritedFixedClaim::from_snapshot(&self)?;
        self.check()?;
        Ok(original)
    }
}

const ORIGINAL_TRANSACTION_WAIT: std::time::Duration = std::time::Duration::from_secs(30);

fn original_transaction(pool: &Pool) -> io::Result<trust_build_cpu::LegacyFixedTransaction<'_>> {
    original_transaction_before(pool, std::time::Instant::now() + ORIGINAL_TRANSACTION_WAIT, || {})
}

fn original_transaction_before(
    pool: &Pool,
    deadline: std::time::Instant,
    mut busy: impl FnMut(),
) -> io::Result<trust_build_cpu::LegacyFixedTransaction<'_>> {
    original_transaction_before_checked(pool, deadline, || {
        busy();
        Ok(())
    })
}

pub(super) fn original_transaction_before_checked(
    pool: &Pool,
    deadline: std::time::Instant,
    mut busy: impl FnMut() -> io::Result<()>,
) -> io::Result<trust_build_cpu::LegacyFixedTransaction<'_>> {
    loop {
        if std::time::Instant::now() >= deadline {
            return Err(io::Error::new(
                io::ErrorKind::TimedOut,
                "original fixed domain stayed busy",
            ));
        }
        match pool.try_legacy_fixed_transaction() {
            Ok(Some(transaction)) => {
                if std::time::Instant::now() >= deadline {
                    return Err(io::ErrorKind::TimedOut.into());
                }
                return Ok(transaction);
            }
            Ok(None) => busy()?,
            Err(error) if error.kind() == io::ErrorKind::Interrupted => {}
            Err(error) => return Err(error),
        }
        std::thread::sleep(
            std::time::Duration::from_millis(1)
                .min(deadline.saturating_duration_since(std::time::Instant::now())),
        );
    }
}

const MAX_PACKET: u64 = 8 * 1024 * 1024;

#[derive(Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Packet {
    version: u32,
    namespace: Vec<u8>,
    cpus: u32,
    budget: u32,
    record: Vec<u8>,
    files: Vec<Entry>,
}

// A distinct envelope leaves V1's deny_unknown_fields grammar intact. Its
// additional member is bound in ALL actual original CPU records, not merely
// attached to a packet a descendant could manufacture.
#[derive(Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct OutputPacket {
    version: u32,
    original: Packet,
    output: output_member::Wire,
}

struct UniqueRecord(serde_json::Map<String, serde_json::Value>);
impl<'de> serde::Deserialize<'de> for UniqueRecord {
    fn deserialize<D: serde::Deserializer<'de>>(reader: D) -> Result<Self, D::Error> {
        struct Fields;
        impl<'de> serde::de::Visitor<'de> for Fields {
            type Value = UniqueRecord;
            fn expecting(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                formatter.write_str("one original fixed record with unique fields")
            }
            fn visit_map<M: serde::de::MapAccess<'de>>(
                self,
                mut fields: M,
            ) -> Result<Self::Value, M::Error> {
                let mut record = serde_json::Map::new();
                while let Some(field) = fields.next_key::<String>()? {
                    if record.contains_key(&field) {
                        return Err(serde::de::Error::custom(
                            "duplicate original fixed record field",
                        ));
                    }
                    record.insert(field, fields.next_value()?);
                }
                Ok(UniqueRecord(record))
            }
        }
        reader.deserialize_map(Fields)
    }
}

fn decode_packet(bytes: &[u8]) -> io::Result<(Packet, Option<output_member::Wire>)> {
    let value: serde_json::Value = serde_json::from_slice(bytes).map_err(io::Error::other)?;
    match value.get("version").and_then(serde_json::Value::as_u64) {
        Some(1) => {
            serde_json::from_slice(bytes).map(|packet| (packet, None)).map_err(io::Error::other)
        }
        Some(2) => {
            let mut packet: OutputPacket =
                serde_json::from_slice(bytes).map_err(io::Error::other)?;
            if packet.version != 2 || packet.original.version != 1 {
                return Err(invalid("invalid original output member envelope generation"));
            }
            packet.original.version = 2;
            Ok((packet.original, Some(packet.output)))
        }
        _ => Err(invalid("unsupported original fixed envelope generation")),
    }
}

fn packet_record(packet: &Packet, output: Option<&output_member::Wire>) -> io::Result<FixedRecord> {
    if let Some(output) = output {
        let UniqueRecord(mut record) =
            serde_json::from_slice(&packet.record).map_err(io::Error::other)?;
        let digest = record
            .remove("output_member_sha256")
            .ok_or_else(|| invalid("original fixed record has no output member binding"))?;
        let digest: [u8; 32] = serde_json::from_value(digest).map_err(io::Error::other)?;
        if digest != output.digest()? {
            return Err(invalid("output member differs from its original fixed record"));
        }
        serde_json::from_value(serde_json::Value::Object(record)).map_err(io::Error::other)
    } else {
        serde_json::from_slice(&packet.record).map_err(io::Error::other)
    }
}

#[derive(Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Entry {
    path: Vec<u8>,
    descriptor: i32,
    device: u64,
    inode: u64,
    slot: bool,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct FixedRecord {
    native_fixed_version: u32,
    pid: u32,
    supervisor_pid: Option<u32>,
    cmd: String,
    cwd: String,
    cwd_bytes: Vec<u8>,
    started: f64,
    cpu_mode: String,
    cpu_budget: u32,
    machine_cpus: u32,
    minimum_slots: u32,
    pool_slots: u32,
    lease_id: String,
    exclusive: bool,
    claim_file_count: u32,
    claim_files_sha256: [u8; 32],
}

fn original_entries(claim: &FixedClaim) -> io::Result<Vec<Entry>> {
    let mut files = Vec::new();
    for (slot, leases) in [(false, &claim.reservation.held), (true, &claim.reservation.slots)] {
        for lease in leases {
            if !claim.reservation.exclusive && lease.name == "admission.lock" {
                continue;
            }
            lease.check()?;
            let meta = lease.file.metadata()?;
            files.push(Entry {
                path: lease.path().into_os_string().into_vec(),
                descriptor: lease.file.as_raw_fd(),
                device: meta.dev(),
                inode: meta.ino(),
                slot,
            });
        }
    }
    Ok(files)
}

fn fingerprint(files: &[Entry]) -> io::Result<(u32, [u8; 32])> {
    if files.is_empty() || files.len() > MAX_TICKETS + 2 {
        return Err(invalid("fixed original file count exceeds its bound"));
    }
    let mut ordered: Vec<_> = files.iter().collect();
    ordered.sort_by(|left, right| left.path.cmp(&right.path));
    if ordered.windows(2).any(|pair| pair[0].path == pair[1].path) {
        return Err(invalid("duplicate original fixed path"));
    }
    let count = u32::try_from(files.len()).map_err(io::Error::other)?;
    let mut digest = Sha256::new();
    digest.update(b"trust-native-fixed-original-files-v1\0");
    digest.update(count.to_le_bytes());
    for file in ordered {
        let length = u32::try_from(file.path.len()).map_err(io::Error::other)?;
        digest.update(length.to_le_bytes());
        digest.update(&file.path);
        digest.update(file.device.to_le_bytes());
        digest.update(file.inode.to_le_bytes());
        digest.update([u8::from(file.slot)]);
    }
    Ok((count, digest.finalize().into()))
}

pub(super) fn fingerprint_claim(claim: &FixedClaim) -> io::Result<(u32, [u8; 32])> {
    fingerprint(&original_entries(claim)?)
}

/// Owns one command and its original complete claim before its one launch.
pub struct PreparedFixedCommand {
    claim: FixedClaim,
    packet: File,
    command: Command,
    quiet: Option<super::quiet::QuietWindow>,
    // Numeric routing DATA for these same retained originals, not a packet
    // import or an independently reconstructible admission capability.
    #[cfg(all(feature = "native-exec", target_os = "macos", target_arch = "aarch64"))]
    original_descriptors: Vec<i32>,
}

/// Direct-child supervision retaining original fixed resources. Direct-child
/// exit is not arbitrary descendant completion or hosted-root retirement.
/// Dropping a live supervisor cancels and reaps its direct child before release.
#[must_use = "retain the supervisor through the actual child wait"]
pub struct RunningFixedCommand {
    claim: Option<FixedClaim>,
    _packet: File,
    child: Child,
}

struct SpawnedFixedCommand {
    claim: FixedClaim,
    packet: File,
    child: Child,
}

#[cfg(test)]
pub(super) fn spawn_fixture(command: PreparedFixedCommand) -> io::Result<RunningFixedCommand> {
    command.spawn_checked()
}

impl FixedClaim {
    /// Issue a private output member before any descendant work. Only this
    /// actual Root claim can bind its digest into all original fixed records.
    pub fn with_original_output_member(mut self) -> io::Result<Self> {
        self.check_current()?;
        if self.output.is_some() {
            return Err(invalid("original fixed output member was already issued"));
        }
        self.output = Some(output_member::Issued::create()?);
        self.publish_owner(std::process::id(), None)?;
        self.check_current()?;
        Ok(self)
    }

    /// Prepare a shared fixed command with actual original descriptors.
    /// Exclusive launch still requires a native measured quiet-host guard.
    pub fn prepare_command(self, command: Command) -> io::Result<PreparedFixedCommand> {
        self.check_current()?;
        if self.reservation.exclusive {
            return Err(invalid("exclusive launch requires measured quiet-host custody"));
        }
        self.prepare_with_quiet(command, None)
    }

    pub(super) fn prepare_with_quiet(
        mut self,
        mut command: Command,
        quiet: Option<super::quiet::QuietWindow>,
    ) -> io::Result<PreparedFixedCommand> {
        self.check_current()?;
        if self.reservation.exclusive != quiet.is_some() {
            return Err(invalid("exclusive command requires its live quiet-host observation"));
        }
        if command.get_envs().any(|(key, _)| key == FIXED_HANDOFF_ENV) {
            return Err(invalid("command overrides its fixed descriptor handoff"));
        }
        if command
            .get_envs()
            .any(|(key, value)| key == jobserver_utils::FIXED_CLAIM_HANDOFF_ENV && value.is_some())
        {
            return Err(invalid("command overrides its original fixed descendant courier"));
        }
        // A new directly owned claim cannot inherit an ancestor's courier:
        // new readers prefer that purpose and would otherwise select it over
        // the complete direct packet installed below.
        command.env_remove(jobserver_utils::FIXED_CLAIM_HANDOFF_ENV);
        let files = original_entries(&self)?;
        let configured = command
            .get_envs()
            .find(|(key, _)| *key == "CARGO_BUILD_JOBS")
            .map(|(_, value)| value.map(OsStr::to_owned));
        let requested = match configured {
            Some(value) => value,
            None => std::env::var_os("CARGO_BUILD_JOBS"),
        };
        let budget = match requested {
            Some(value) => {
                let requested = value
                    .to_str()
                    .filter(|text| !text.is_empty() && text.bytes().all(|b| b.is_ascii_digit()))
                    .and_then(|text| text.parse::<u32>().ok())
                    .filter(|value| *value > 0)
                    .ok_or_else(|| {
                        invalid("fixed command CPU request must be a positive integer")
                    })?;
                requested.min(self.budget.get())
            }
            None => self.budget.get(),
        };
        if budget < self.budget.get() {
            // Shrinking frees only the unused declared share. Publish it in
            // ALL original held records so nested readers cannot recover the
            // previous larger ceiling from their inherited descriptions.
            self.budget = NonZeroU32::new(budget).unwrap();
            self.publish_owner(std::process::id(), None)?;
        }
        command.env("CARGO_BUILD_JOBS", budget.to_string());
        let description = Packet {
            version: 1,
            namespace: self.reservation.namespace.as_os_str().as_bytes().to_vec(),
            cpus: self.cpus.get(),
            budget: self.budget.get(),
            record: self.record.clone(),
            files,
        };
        let output = self.output.as_ref().map(output_member::Issued::wire).transpose()?;
        let output_descriptors = output.as_ref().map(output_member::Wire::descriptors);
        if let Some(output) = self.output.as_ref() {
            // Routing only. The member's originals and record digest, never
            // TMPDIR's pathname, establish output membership.
            command.env("TMPDIR", output.root()?);
        }
        let bytes = match output {
            Some(output) => {
                serde_json::to_vec(&OutputPacket { version: 2, original: description, output })
            }
            None => serde_json::to_vec(&description),
        }
        .map_err(io::Error::other)?;
        if bytes.len() as u64 > MAX_PACKET {
            return Err(invalid("fixed descriptor handoff exceeds its bound"));
        }
        let mut packet = private_packet()?;
        packet.write_all(&bytes)?;
        packet.flush()?;
        command.env(FIXED_HANDOFF_ENV, packet.as_raw_fd().to_string());
        let descriptors: Vec<_> = original_entries(&self)?
            .iter()
            .map(|file| file.descriptor)
            .chain(std::iter::once(packet.as_raw_fd()))
            .chain(output_descriptors.into_iter().flatten())
            .collect();
        #[cfg(all(feature = "native-exec", target_os = "macos", target_arch = "aarch64"))]
        let original_descriptors = descriptors.clone();
        // SAFETY: this owner retains the original files through spawn. Only
        // async-signal-safe descriptor operations run in the forked child.
        unsafe {
            command.pre_exec(move || {
                for &descriptor in &descriptors {
                    let flags = libc::fcntl(descriptor, libc::F_GETFD);
                    if flags < 0
                        || libc::fcntl(descriptor, libc::F_SETFD, flags & !libc::FD_CLOEXEC) < 0
                    {
                        return Err(io::Error::last_os_error());
                    }
                }
                Ok(())
            });
        }
        Ok(PreparedFixedCommand {
            claim: self,
            packet,
            command,
            quiet,
            #[cfg(all(feature = "native-exec", target_os = "macos", target_arch = "aarch64"))]
            original_descriptors,
        })
    }
}

impl PreparedFixedCommand {
    /// Revalidate canonical original claim and CPU room, then spawn once.
    pub fn spawn(self) -> io::Result<RunningFixedCommand> {
        match self.claim.observe_native_room_before(
            std::time::Instant::now() + ORIGINAL_TRANSACTION_WAIT,
            || Ok(()),
        )? {
            LegacyFixedRoom::Fits { .. } => self.spawn_checked(),
            room => Err(io::Error::new(
                io::ErrorKind::WouldBlock,
                format!("native fixed child prelaunch refused: {room:?}"),
            )),
        }
    }

    fn spawn_checked(self) -> io::Result<RunningFixedCommand> {
        let spawned = self.launch_checked()?;
        Ok(RunningFixedCommand {
            claim: Some(spawned.claim),
            _packet: spawned.packet,
            child: spawned.child,
        })
    }

    fn launch_checked(mut self) -> io::Result<SpawnedFixedCommand> {
        self.claim.check_current()?;
        if let Some(quiet) = self.quiet.as_mut() {
            quiet.check(&self.claim)?;
        }
        let child = self.command.spawn()?;
        // std returned only after the child's successful exec. CPU/worktree
        // ownership stays with the supervisor; only prelaunch exclusion ends.
        self.claim.release_prelaunch_admission();
        Ok(SpawnedFixedCommand { claim: self.claim, packet: self.packet, child })
    }
}

impl RunningFixedCommand {
    /// Move the actual direct child's stdout stream to its owning consumer.
    pub fn take_stdout(&mut self) -> Option<std::process::ChildStdout> {
        self.child.stdout.take()
    }

    /// Move the actual direct child's stderr stream to its owning consumer.
    pub fn take_stderr(&mut self) -> Option<std::process::ChildStderr> {
        self.child.stderr.take()
    }

    /// PID of the actual direct child, for its owning supervisor.
    pub fn id(&self) -> u32 {
        self.child.id()
    }

    /// Wait for this direct child while retaining all original resources.
    pub fn wait(&mut self) -> io::Result<ExitStatus> {
        self.claim.as_ref().expect("live fixed command claim").check_current()?;
        self.child.wait()
    }

    /// Observe and reap only this actual direct child, keeping its claim live.
    pub fn try_wait(&mut self) -> io::Result<Option<ExitStatus>> {
        self.claim.as_ref().expect("live fixed command claim").check_current()?;
        self.child.try_wait()
    }

    /// Cancel this owner's direct child and perform its actual wait. Resource
    /// validation cannot prevent cancellation of a command we already own.
    /// An exit racing the kill is accepted only through the owning wait.
    pub fn cancel(&mut self) -> io::Result<ExitStatus> {
        if let Some(status) = self.child.try_wait()? {
            return Ok(status);
        }
        if let Err(error) = self.child.kill() {
            return match self.child.try_wait()? {
                Some(status) => Ok(status),
                None => Err(error),
            };
        }
        self.child.wait()
    }
}

impl Drop for RunningFixedCommand {
    fn drop(&mut self) {
        if let Err(error) = self.cancel() {
            // Unknown retirement must not turn into free CPU/worktree room.
            // Preserve the actual originals for this process's remaining
            // lifetime; no path, PID or saved status can replace that custody.
            if let Some(claim) = self.claim.take() {
                std::mem::forget(claim);
            }
            let _ = writeln!(
                io::stderr().lock(),
                "native fixed command retirement is unknown; original resources retained: {error}"
            );
        }
    }
}

/// Duplicate custody validated against every original kernel-held claim file.
/// Public PID, path and budget data cannot construct this value by themselves.
pub struct InheritedFixedClaim {
    held: Vec<HeldLease>,
    record: Vec<u8>,
    budget: NonZeroU32,
    wire: Vec<u8>,
    descendants: std::sync::OnceLock<jobserver_utils::FixedClaimHandoff>,
    output: Option<output_member::Retained>,
    output_directories: std::sync::Mutex<Vec<std::sync::Arc<MemberDirectory>>>,
}

impl std::fmt::Debug for InheritedFixedClaim {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter
            .debug_struct("InheritedFixedClaim")
            .field("budget", &self.budget)
            .field("held_files", &self.held.len())
            .finish_non_exhaustive()
    }
}

impl InheritedFixedClaim {
    /// Current ceiling bound to all retained original claim files.
    pub fn budget(&self) -> io::Result<NonZeroU32> {
        self.check_current()?;
        Ok(self.budget)
    }

    /// A caller hint can only reduce the actual retained original ceiling.
    /// This does not publish a record, acquire resources or construct a claim.
    pub fn limited_budget(&self, hint: Option<&OsStr>) -> io::Result<NonZeroU32> {
        let original = self.budget()?;
        let Some(hint) = hint else { return Ok(original) };
        let limit = hint
            .to_str()
            .filter(|text| !text.is_empty() && text.bytes().all(|byte| byte.is_ascii_digit()))
            .and_then(|text| text.parse::<NonZeroU32>().ok())
            .ok_or_else(|| invalid("fixed caller CPU ceiling must be a positive integer"))?;
        Ok(original.min(limit))
    }

    /// Validate the advertised originals against the existing canonical pool.
    /// The advertised descriptors are never closed or modified by this reader.
    pub fn from_descriptor(value: &OsStr) -> io::Result<Self> {
        EarlyFixedClaim::snapshot(value)?.capture()
    }

    fn from_snapshot(pending: &EarlyFixedClaim) -> io::Result<Self> {
        let packet = trust_build_cpu::duplicate_descriptor(&pending.descriptor)?;
        let (legacy, _) = trust_build_cpu::LegacyRetirement::canonical_layout()?;
        let pool = Pool::open_existing(&trust_build_cpu::capacity_dir()?)?
            .ok_or_else(|| invalid("original native CPU pool is unavailable"))?;
        let _transaction = original_transaction(&pool)?;
        pending.check()?;
        Self::read_file(packet, &fs::canonicalize(legacy)?, pool.slots(), None)
    }

    #[cfg(test)]
    fn read(value: &OsStr, namespace: &Path, width: NonZeroU32) -> io::Result<Self> {
        let packet_file = trust_build_cpu::duplicate_descriptor(value)?;
        Self::read_file(packet_file, namespace, width, None)
    }

    /// Import a distinct live ancestor courier. Advertised numeric descriptors
    /// in its packet are never read, closed or interpreted in this process.
    /// The same complete domain validation applies to the fresh SCM rights.
    pub fn from_descendant(advertisement: &OsStr) -> io::Result<Self> {
        // Authenticate once and retain these SAME rights while the existing
        // domain transaction is busy. No reconnect/reimport or new claim.
        let (packet, originals) = jobserver_utils::recover_fixed_claim(advertisement)?;
        let (legacy, _) = trust_build_cpu::LegacyRetirement::canonical_layout()?;
        let pool = Pool::open_existing(&trust_build_cpu::capacity_dir()?)?
            .ok_or_else(|| invalid("original native CPU pool is unavailable"))?;
        let _transaction = original_transaction(&pool)?;
        Self::read_file(packet.into(), &fs::canonicalize(legacy)?, pool.slots(), Some(originals))
    }

    fn read_file(
        packet_file: File,
        namespace: &Path,
        width: NonZeroU32,
        transferred: Option<Vec<std::os::fd::OwnedFd>>,
    ) -> io::Result<Self> {
        let meta = packet_file.metadata()?;
        if !meta.is_file()
            || meta.uid() != unsafe { libc::geteuid() }
            || meta.mode() & 0o077 != 0
            || meta.len() > MAX_PACKET
        {
            return Err(invalid("unsafe fixed handoff packet"));
        }
        let mut bytes = vec![0; meta.len() as usize];
        packet_file.read_exact_at(&mut bytes, 0)?;
        let (packet, output) = decode_packet(&bytes)?;
        let output_count = if output.is_some() { 2 } else { 0 };
        if transferred.as_ref().is_some_and(|fds| fds.len() != packet.files.len() + output_count) {
            return Err(invalid(
                "transferred fixed claim has a different original file population",
            ));
        }
        if !matches!(packet.version, 1 | 2)
            || packet.cpus != width.get()
            || packet.budget == 0
            || packet.budget > width.get()
            || packet.record.len() as u64 > MAX_RECORD
            || packet.files.is_empty()
            || packet.files.len() > MAX_TICKETS + 2
            || Path::new(OsStr::from_bytes(&packet.namespace)) != namespace
        {
            return Err(invalid("invalid original fixed handoff"));
        }
        let row = packet_record(&packet, output.as_ref())?;
        let (count, digest) = fingerprint(&packet.files)?;
        if row.native_fixed_version != packet.version
            || row.cpu_mode != "fixed-v1"
            || row.cpu_budget != packet.budget
            || row.machine_cpus != packet.cpus
            || row.minimum_slots == 0
            || row.minimum_slots > trust_build_cpu::MAX_SLOTS
            || row.pool_slots < row.minimum_slots
            || row.pool_slots > trust_build_cpu::MAX_SLOTS
            || row.pid == 0
            || row.supervisor_pid == Some(0)
            || row.cmd.is_empty()
            || !Path::new(&row.cwd).is_absolute()
            || row.cwd_bytes.is_empty()
            || !row.started.is_finite()
            || row.started < 0.0
            || row.lease_id.len() != 32
            || !row.lease_id.bytes().all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
            || row.claim_file_count != count
            || row.claim_files_sha256 != digest
        {
            return Err(invalid("fixed handoff disagrees with its complete original record"));
        }
        let mut held = Vec::new();
        let mut identities = BTreeSet::new();
        let mut slot_count = 0_u64;
        let mut slot_members = BTreeSet::new();
        let mut exclusive_fence = false;
        let mut transferred = transferred.map(Vec::into_iter);
        for entry in packet.files {
            let path = PathBuf::from(OsString::from_vec(entry.path));
            validate_path(&path)?;
            let parent = path.parent().ok_or_else(|| invalid("fixed lease has no parent"))?;
            let name =
                path.file_name().ok_or_else(|| invalid("fixed lease has no name"))?.to_owned();
            if entry.slot {
                let index = name
                    .to_str()
                    .and_then(|name| name.strip_prefix("slot-"))
                    .filter(|tail| !tail.is_empty() && tail.bytes().all(|b| b.is_ascii_digit()))
                    .and_then(|tail| tail.parse::<u32>().ok());
                if parent != namespace || !index.is_some_and(|index| index < row.pool_slots) {
                    return Err(invalid("fixed slot is outside its original namespace"));
                }
                slot_count += 1;
                slot_members.insert(name.clone());
            } else if parent == namespace && name == "admission.lock" {
                if !row.exclusive || exclusive_fence {
                    return Err(invalid("shared handoff cannot claim an exclusive fence"));
                }
                exclusive_fence = true;
            }
            let file = if let Some(originals) = transferred.as_mut() {
                File::from(originals.next().ok_or_else(|| invalid("missing transferred original"))?)
            } else {
                trust_build_cpu::duplicate_descriptor(OsStr::new(&entry.descriptor.to_string()))?
            };
            let directory = Directory::open(parent)?;
            directory.check_file(&name, &file)?;
            let meta = file.metadata()?;
            if (meta.dev(), meta.ino()) != (entry.device, entry.inode)
                || !identities.insert((entry.device, entry.inode))
            {
                return Err(invalid("fixed handoff original file identity disagrees"));
            }
            let probe = directory.open_file(&name, false)?;
            match probe.try_lock_shared() {
                Ok(()) => return Err(invalid("fixed handoff is not exclusively held")),
                Err(std::fs::TryLockError::WouldBlock) => {}
                Err(std::fs::TryLockError::Error(error)) => return Err(error),
            }
            if file.try_lock().is_err() {
                return Err(invalid("fixed handoff is held by a foreign open description"));
            }
            if read_record(&file)? != packet.record {
                return Err(invalid("fixed handoff original record changed"));
            }
            held.push(HeldLease { directory, name, file });
        }
        if row.exclusive {
            let directory = Directory::open(namespace)?;
            let expected: BTreeSet<_> =
                slot_names(&directory, row.minimum_slots)?.into_iter().collect();
            if !exclusive_fence || slot_members != expected {
                return Err(invalid(
                    "exclusive handoff omits an original fence or historical slot",
                ));
            }
            directory.check()?;
        }
        let share = u64::from(row.machine_cpus) * slot_count / u64::from(row.minimum_slots);
        if slot_count == 0 || u64::from(row.cpu_budget) > share.max(1) {
            return Err(invalid("fixed handoff exceeds its actual original slot share"));
        }
        let output = output
            .map(|wire| {
                let originals = transferred
                    .as_mut()
                    .map(|originals| {
                        let directory = originals
                            .next()
                            .ok_or_else(|| invalid("missing output directory original"))?;
                        let lock = originals
                            .next()
                            .ok_or_else(|| invalid("missing output lock original"))?;
                        Ok::<_, io::Error>([directory, lock])
                    })
                    .transpose()?;
                output_member::Retained::capture(wire, originals)
            })
            .transpose()?;
        Ok(Self {
            held,
            record: packet.record,
            budget: NonZeroU32::new(packet.budget).unwrap(),
            wire: bytes,
            descendants: std::sync::OnceLock::new(),
            output,
            output_directories: std::sync::Mutex::new(Vec::new()),
        })
    }

    /// Close-only originals for the private native maintenance subgroup. This
    /// never constructs a claim or changes its existing resource allocation.
    #[cfg(all(feature = "native-exec", target_os = "macos", target_arch = "aarch64"))]
    pub(crate) fn maintenance_originals(&self) -> io::Result<Vec<std::os::fd::BorrowedFd<'_>>> {
        use std::os::fd::AsFd as _;
        self.check_current()?;
        Ok(self
            .held
            .iter()
            .map(|held| held.file.as_fd())
            .chain(self.output.iter().flat_map(output_member::Retained::descriptors))
            .collect())
    }

    /// Serve the actual originals across unaware std/build-script spawns.
    /// This creates no new claim; the endpoint retains the SAME descriptions.
    pub fn descendant_advertisement(&self) -> io::Result<&OsStr> {
        self.check_current()?;
        if self.descendants.get().is_none() {
            let mut originals = self
                .held
                .iter()
                .map(|lease| lease.file.try_clone().map(Into::into))
                .collect::<io::Result<Vec<std::os::fd::OwnedFd>>>()?;
            if let Some(output) = &self.output {
                for original in output.descriptors() {
                    originals.push(original.try_clone_to_owned()?);
                }
            }
            let mut packet = private_packet()?;
            packet.write_all(&self.wire)?;
            packet.flush()?;
            self.check_current()?;
            let endpoint = if self.output.is_some() {
                jobserver_utils::FixedClaimHandoff::new_with_output_member(
                    packet.into(),
                    originals,
                )?
            } else {
                jobserver_utils::FixedClaimHandoff::new(packet.into(), originals)?
            };
            let _ = self.descendants.set(endpoint);
        }
        self.check_current()?;
        Ok(self.descendants.get().expect("installed original fixed courier").advertisement())
    }

    /// A nested command can retain or reduce the parent's actual ceiling.
    pub fn check_budget(&self, requested: NonZeroU32) -> io::Result<()> {
        self.check_current()?;
        if requested > self.budget {
            return Err(invalid("nested command exceeds its original fixed CPU budget"));
        }
        Ok(())
    }

    // Trust: this check reads only the claim's own packet and record, so it
    // lives with the claim, not with the Apple-silicon nested launcher
    // (handoff/nested.rs) it was first written beside. Targo's `repo-prune`
    // calls it on Linux too (src/tools/targo/src/bin/cargo/resource_prune.rs).
    /// Continue only in the same actual worktree and within the original CPU
    /// ceiling. A requested exclusive continuation needs the already-held
    /// original fence; this observation never acquires or upgrades a claim.
    pub fn check_nested(
        &self,
        budget: NonZeroU32,
        worktree: Option<&Path>,
        exclusive: bool,
    ) -> io::Result<()> {
        self.check_budget(budget)?;
        let (packet, output) = decode_packet(&self.wire)?;
        if output.is_some() && worktree.is_none() {
            return Err(invalid(
                "V2 continuation needs its actual source worktree or typed output member",
            ));
        }
        let record = packet_record(&packet, output.as_ref())?;
        let admission = PathBuf::from(OsString::from_vec(packet.namespace)).join("admission.lock");
        let original_worktrees = packet
            .files
            .iter()
            .filter(|entry| !entry.slot)
            .map(|entry| PathBuf::from(OsString::from_vec(entry.path.clone())))
            .filter(|path| path != &admission)
            .collect::<Vec<_>>();
        if original_worktrees.iter().map(PathBuf::as_path).ne(worktree) {
            return Err(invalid("nested command does not hold this original worktree lock"));
        }
        if exclusive && !record.exclusive {
            return Err(invalid("nested command cannot upgrade shared original admission"));
        }
        self.check_current()
    }

    /// Open an actual cwd/target directory under the Root-issued member.
    /// V1 has no member and supplies no substitute or wildcard authority.
    pub fn original_output_directory(&self, path: &Path) -> io::Result<Option<MemberDirectory>> {
        self.check_current()?;
        self.output.as_ref().map(|output| output.directory(path)).transpose()
    }

    /// Prepare output directories through the SAME Root descriptor. Existing
    /// symlinks, escapes or foreign-member paths are errors, never repaired.
    pub fn prepare_original_output_directory(
        &self,
        path: &Path,
    ) -> io::Result<Option<MemberDirectory>> {
        self.check_current()?;
        self.output.as_ref().map(|output| output.prepare_directory(path)).transpose()
    }

    /// Retain actual prepared target/build directories with this SAME original
    /// continuation. Every later claim check also checks these original names;
    /// a returned observation never replaces their live descriptions.
    pub fn retain_original_output_directory(
        &self,
        path: &Path,
    ) -> io::Result<std::sync::Arc<MemberDirectory>> {
        let directory = std::sync::Arc::new(
            self.prepare_original_output_directory(path)?
                .ok_or_else(|| invalid("V1 cannot retain a Root output member"))?,
        );
        self.retain_output_directory(directory)
    }

    /// An existing workspace/source directory inside the member is retained
    /// without creation. `None` gives no permission: the caller must instead
    /// match the actual selected source's original worktree, never its cwd.
    pub fn retain_existing_output_source_directory(
        &self,
        path: &Path,
    ) -> io::Result<Option<std::sync::Arc<MemberDirectory>>> {
        self.check_current()?;
        let directory =
            self.output.as_ref().map(|output| output.source_directory(path)).transpose()?.flatten();
        directory
            .map(|directory| self.retain_output_directory(std::sync::Arc::new(directory)))
            .transpose()
    }

    /// Check member ancestry/kind only. Existing source-input ownership still
    /// owns parsed bytes, revisions and currency; this confers no source grade.
    pub fn check_output_source_file(
        &self,
        directory: &MemberDirectory,
        name: &OsStr,
    ) -> io::Result<()> {
        self.check_current()?;
        self.output
            .as_ref()
            .ok_or_else(|| invalid("V1 has no source output member"))?
            .check_source_file(directory, name)
    }

    fn retain_output_directory(
        &self,
        directory: std::sync::Arc<MemberDirectory>,
    ) -> io::Result<std::sync::Arc<MemberDirectory>> {
        let mut retained = self
            .output_directories
            .lock()
            .map_err(|_| invalid("original output directory retention is poisoned"))?;
        for original in retained.iter() {
            if original.same_member_directory(&directory) {
                self.output.as_ref().expect("same original member").check_directory(original)?;
                return Ok(original.clone());
            }
        }
        if retained.len() >= MAX_TICKETS {
            return Err(invalid("complete retained output directory population exceeds its bound"));
        }
        retained.push(directory.clone());
        Ok(directory)
    }

    /// Retain the actual current cwd when it belongs to this original member.
    /// `None` supplies no permission: source/worktree admission stays separate.
    pub fn original_output_cwd(&self) -> io::Result<Option<MemberDirectory>> {
        use std::os::unix::fs::OpenOptionsExt as _;
        self.check_current()?;
        let Some(output) = &self.output else { return Ok(None) };
        let actual = fs::OpenOptions::new()
            .read(true)
            .custom_flags(libc::O_DIRECTORY | libc::O_NOFOLLOW | libc::O_CLOEXEC)
            .open(".")?;
        let path = std::env::current_dir()?;
        let root = output.root();
        if !path.starts_with(root) {
            return Ok(None);
        }
        let member = output.directory(&path)?;
        if !member.matches(&actual)? {
            return Err(invalid("actual cwd changed during original output member capture"));
        }
        self.check_output_directory(&member)?;
        Ok(Some(member))
    }

    /// Generation observation only, never permission to run a workload.
    pub fn has_original_output_member(&self) -> io::Result<bool> {
        self.check_current()?;
        Ok(self.output.is_some())
    }

    pub fn check_output_directory(&self, directory: &MemberDirectory) -> io::Result<()> {
        self.check_current()?;
        self.output
            .as_ref()
            .ok_or_else(|| invalid("V1 has no original output member"))?
            .check_directory(directory)?;
        self.check_current()
    }

    // Only `nested`, compiled under the same gate, calls this.
    #[cfg(all(feature = "native-exec", target_os = "macos", target_arch = "aarch64"))]
    fn check_output_nested(
        &self,
        budget: NonZeroU32,
        directory: &MemberDirectory,
        exclusive: bool,
    ) -> io::Result<()> {
        self.check_budget(budget)?;
        self.check_output_directory(directory)?;
        let (packet, output) = decode_packet(&self.wire)?;
        if exclusive && !packet_record(&packet, output.as_ref())?.exclusive {
            return Err(invalid("output continuation cannot upgrade shared original admission"));
        }
        self.check_current()
    }

    /// Retain and revalidate only originals; never adopt replacements.
    pub fn check_current(&self) -> io::Result<()> {
        if let Some(output) = &self.output {
            output.check()?;
            let directories = self
                .output_directories
                .lock()
                .map_err(|_| invalid("original output directory retention is poisoned"))?;
            for directory in directories.iter() {
                output.check_directory(directory)?;
            }
        }
        for lease in &self.held {
            lease.check()?;
            if read_record(&lease.file)? != self.record {
                return Err(invalid("inherited original fixed record changed"));
            }
        }
        Ok(())
    }
}

#[cfg(test)]
#[path = "handoff/tests.rs"]
mod tests;
