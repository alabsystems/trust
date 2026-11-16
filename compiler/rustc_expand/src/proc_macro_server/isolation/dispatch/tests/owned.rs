//! Trust (PM-1): the real compiler Dispatcher uses B3's original Session and
//! owned static child. This is a Linux prerequisite test, not a native DSO,
//! constructor-containment qualification, or an enabled macro provider.
use std::fs::File;
use std::os::fd::{AsRawFd, FromRawFd};
use std::os::unix::fs::PermissionsExt;
use std::sync::atomic::{AtomicU64, Ordering};

use sha2::{Digest, Sha256};
use trust_worker_linux::KernelLimits;
use trust_worker_linux::launcher::{
    InputClosureIdentity, InputSource, LaunchLimits, Outcome, PreparedStaticWorker,
};
use trust_worker_linux::native::{
    NativeClosure, NativeObjectPlan, NativeRole, digest as native_digest,
};

use super::*;

struct Scratch(std::path::PathBuf);
impl Drop for Scratch {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir(&self.0);
    }
}

fn exchange(mode: &str, sabotage: u8, with_native: bool) {
    let mut allowance = limits();
    allowance.work = 1 << 30;
    let budget = Budget::new(allowance, Instant::now() + Duration::from_secs(30)).unwrap();
    let fixture = std::env::var("TRUST_STATIC_WORKER_FIXTURE")
        .expect("set the independently built native static ET_EXEC fixture");
    let bytes = std::fs::read(&fixture).unwrap();
    let executable = File::open(&fixture).unwrap();
    let worker = InputSource {
        file: &executable,
        sha256: Sha256::digest(&bytes).into(),
        size: bytes.len() as u64,
        executable: true,
    };
    static NEXT: AtomicU64 = AtomicU64::new(1);
    let path = std::env::temp_dir().join(format!(
        "trust-dispatcher-owned-{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    ));
    std::fs::create_dir(&path).unwrap();
    std::fs::set_permissions(&path, std::fs::Permissions::from_mode(0o700)).unwrap();
    let scratch = Scratch(path);
    let input_path = scratch.0.join("input");
    std::fs::write(&input_path, [b'p'; 4096]).unwrap();
    let input_file = File::open(&input_path).unwrap();
    std::fs::remove_file(input_path).unwrap();
    let inputs = [InputSource {
        file: &input_file,
        sha256: Sha256::digest([b'p'; 4096]).into(),
        size: 4096,
        executable: false,
    }];
    let directory_name = std::ffi::CString::new(scratch.0.as_os_str().as_encoded_bytes()).unwrap();
    // SAFETY: this fresh fixture-owned directory has a live terminated path.
    let fd = unsafe {
        libc::open(directory_name.as_ptr(), libc::O_PATH | libc::O_DIRECTORY | libc::O_CLOEXEC)
    };
    assert!(fd >= 0);
    // SAFETY: the successful open returned this uniquely owned descriptor.
    let directory = unsafe { File::from_raw_fd(fd) };
    let native_path = with_native.then(|| {
        std::env::var("TRUST_NATIVE_OBJECT_FIXTURE")
            .expect("set the independently built native ELF DSO fixture")
    });
    let native_file = native_path.as_ref().map(File::open).transpose().unwrap();
    let native_bytes = native_path.as_ref().map(std::fs::read).transpose().unwrap();
    let native_plans = native_file.as_ref().zip(native_bytes.as_ref()).map(|(file, bytes)| {
        [NativeObjectPlan {
            source: InputSource {
                file,
                sha256: Sha256::digest(bytes).into(),
                size: bytes.len() as u64,
                executable: true,
            },
            role: NativeRole::Macro,
            soname: "libfixture.so",
            needed: &[],
            aliases: &["/trust-cap/libfixture.so"],
        }]
    });
    let native_graph =
        native_plans.as_ref().map(|plans| native_digest(plans, 64 << 20, &budget).unwrap());
    let input_identity = InputClosureIdentity::from_plan(&worker, &inputs, native_graph).unwrap();
    let mut identity = binding();
    identity.worker = worker.sha256;
    identity.input_closure = input_identity.digest();
    if let Some(plans) = &native_plans {
        identity.artifact = plans[0].source.sha256;
    }

    with_unstarted_dispatcher(budget.clone(), identity, |d, session, _, _| {
        let original = session.owner();
        let input = d.server.ts_from_str("alpha beta").unwrap();
        let input = d.store_input(input).unwrap();
        let begin = Envelope {
            binding: session.binding().clone(),
            message: Message::Begin {
                declaration: 0,
                kind: 0,
                inputs: vec![input],
                globals: d.globals(),
            },
        };
        let native = native_plans.as_ref().map(|plans| {
            NativeClosure::prepare(plans, input_identity, &session, 64 << 20).unwrap()
        });
        let prepared = PreparedStaticWorker::prepare(
            &worker,
            &inputs,
            native,
            &session,
            LaunchLimits {
                kernel: KernelLimits {
                    address_space_bytes: 256 * 1024 * 1024,
                    stack_bytes: 8 * 1024 * 1024,
                    file_bytes: 1024 * 1024,
                    descriptors: 64,
                },
                sampled_leader_rss_bytes: 128 * 1024 * 1024,
                output_bytes_per_stream: 8192,
                input_bytes: 64 * 1024 * 1024,
            },
        )
        .unwrap();
        let hex = inputs[0].sha256.iter().map(|b| format!("{b:02x}")).collect::<String>();
        // SAFETY: reserve one fresh ambient descriptor for the existing static
        // fixture's pre-entry inherited-descriptor negative check.
        let canary = unsafe { libc::fcntl(input_file.as_raw_fd(), libc::F_DUPFD_CLOEXEC, 40) };
        assert!(canary >= 0);
        // SAFETY: successful duplication returned this uniquely owned canary.
        let _canary = unsafe { File::from_raw_fd(canary) };
        let owned = prepared
            .launch(&[mode, &hex, &canary.to_string()], &directory, begin, session)
            .unwrap();
        let pid = owned.pid();
        let mut calls = Vec::new();
        let receipt = owned
            .run(|call, session| {
                assert!(original.matches(session));
                assert!(budget.shares_owner(session.budget()));
                calls.push(call.method);
                if sabotage == 1 {
                    // Numerically equal metadata and the SAME Budget still
                    // cannot replace the compiler's original SessionOwner.
                    let mut replacement =
                        Session::new(session.binding().clone(), budget.clone()).unwrap();
                    return d
                        .dispatch(&mut replacement, call)
                        .map_err(trust_worker_linux::Error::Budget);
                }
                if sabotage == 2 {
                    budget.cancel();
                }
                d.dispatch(session, call).map_err(trust_worker_linux::Error::Budget)
            })
            .unwrap();
        assert!(receipt.reaped);
        // SAFETY: this exact child belongs to this test; successful ownership
        // teardown must already have consumed its wait status.
        assert_eq!(unsafe { libc::waitpid(pid as i32, std::ptr::null_mut(), libc::WNOHANG) }, -1);
        assert_eq!(std::io::Error::last_os_error().raw_os_error(), Some(libc::ECHILD));
        if mode == "dispatcher" && sabotage == 0 {
            assert_eq!(receipt.outcome, Outcome::Finished);
            assert_eq!(
                calls,
                [Method::TsClone, Method::TsToString, Method::SpanSourceText, Method::TsDrop]
            );
            let output = d.tokens.stream(receipt.output.unwrap()).unwrap();
            assert_eq!(d.server.ts_to_string(&output), "alpha beta");
            assert!(d.tokens.stream(input).is_err());
            assert!(budget.check().is_ok());
            assert_eq!(receipt.input_identity, input_identity);
            assert_eq!(receipt.binding.input_closure, input_identity.digest());
            if let Some(plans) = &native_plans {
                let native = receipt.native.as_ref().unwrap();
                assert_eq!(native.identity, input_identity);
                assert_eq!(Some(native.graph_digest), native_graph);
                assert_eq!(native.objects.len(), 1);
                assert_eq!(native.objects[0].input.sha256, plans[0].source.sha256);
                assert_eq!(native.objects[0].role, NativeRole::Macro);
                assert_eq!(receipt.input_bytes, worker.size + inputs[0].size + native.input_bytes);
            } else {
                assert!(receipt.native.is_none());
            }
        } else {
            assert_ne!(receipt.outcome, Outcome::Finished);
            assert!(receipt.output.is_none());
            assert!(budget.check().is_err());
            if sabotage != 0 || mode == "dispatcher-stale" {
                assert!(!calls.is_empty());
            }
        }
    });
}

#[test]
#[ignore = "requires native Linux and separately built static ET_EXEC TRUST_STATIC_WORKER_FIXTURE"]
fn compiler_dispatcher_and_owned_child_share_the_original_session() {
    exchange("dispatcher", 0, false);
}

#[test]
#[ignore = "requires native Linux and separately built static ET_EXEC TRUST_STATIC_WORKER_FIXTURE"]
fn owned_compiler_dispatch_refuses_substitution_stale_handles_and_cancel_and_reaps() {
    exchange("dispatcher", 1, false);
    exchange("dispatcher", 2, false);
    exchange("dispatcher-stale", 0, false);
    exchange("partial", 0, false);
    exchange("abnormal", 0, false);
}

#[test]
#[ignore = "requires native Linux, static TRUST_STATIC_WORKER_FIXTURE and ELF DSO TRUST_NATIVE_OBJECT_FIXTURE"]
fn compiler_dispatcher_receipts_the_bound_native_graph_with_the_owned_child() {
    exchange("dispatcher", 0, true);
}
