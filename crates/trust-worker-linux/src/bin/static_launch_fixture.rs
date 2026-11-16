//! Trusted diagnostic only. Build as static ET_EXEC; no native DSO is loaded.
use std::time::{Duration, Instant};

use trust_process_isolation::{Budget, Call, Envelope, Limits, Message, Method, Transport, Value};
use trust_worker_linux::{KernelLimits, PinnedInput, Profile, install};

fn exit(code: i32) -> ! {
    // SAFETY: fixture-only terminal exit closes retained descriptors in kernel
    // teardown, without destructors issuing forbidden retained-FD closes.
    unsafe { libc::_exit(code) }
}
fn emit(fd: i32, bytes: &[u8]) {
    // SAFETY: initialized bytes remain live for the supplied length; fd is a
    // declared write-only diagnostic or read/write control capability.
    if unsafe { libc::write(fd, bytes.as_ptr().cast(), bytes.len()) } != bytes.len() as isize {
        exit(71)
    }
}
fn main() {
    let args: Vec<_> = std::env::args().collect();
    if args.len() != 4 || std::env::vars_os().next().is_some() {
        exit(70)
    }
    let mut hash = [0; 32];
    if args[2].len() != 64 {
        exit(70)
    }
    for (at, byte) in hash.iter_mut().enumerate() {
        let Ok(n) = u8::from_str_radix(&args[2][2 * at..2 * at + 2], 16) else { exit(70) };
        *byte = n;
    }
    let Ok(canary) = args[3].parse::<i32>() else { exit(70) };
    // SAFETY: observe that launcher closed this deliberately inherited canary
    // before any worker body or restriction helper can create another descriptor.
    if unsafe { libc::fcntl(canary, libc::F_GETFD) } >= 0 {
        exit(70)
    }
    // SAFETY: read only the B3 launcher's authenticated control role before
    // entry can set its flags. This independently tests trusted birth setup.
    let control_flags = unsafe { libc::fcntl(3, libc::F_GETFL) };
    if control_flags < 0 || control_flags & libc::O_NONBLOCK == 0 {
        exit(70)
    }
    let budget = Budget::new(
        Limits {
            frame_bytes: 65536,
            wire_bytes: 2_000_000,
            allocation_bytes: 2_000_000,
            values: 10000,
            work: 100_000_000,
            calls: 100,
            live_handles: 64,
            depth: 16,
        },
        Instant::now()
            + if args[1] == "control-deadline" {
                Duration::from_secs(2)
            } else {
                Duration::from_secs(30)
            },
    )
    .unwrap_or_else(|_| exit(70));
    // SAFETY: getppid only observes the authoritative parent of this worker.
    let parent = unsafe { libc::getppid() };
    let inputs = [PinnedInput { fd: 5, sha256: hash, size: 4096, executable: false }];
    let profile = Profile {
        parent_pid: parent,
        inputs: &inputs,
        limits: KernelLimits {
            address_space_bytes: 256 * 1024 * 1024,
            stack_bytes: 8 * 1024 * 1024,
            file_bytes: 1024 * 1024,
            descriptors: 64,
        },
    };
    let mut installed = install(&profile, &budget).unwrap_or_else(|_| exit(72));
    let mut control = installed.control().unwrap_or_else(|_| exit(73));
    let frame = control.receive(&budget).unwrap_or_else(|_| exit(73));
    let Ok(begin) = trust_process_isolation::decode(&frame, &budget) else { exit(73) };
    if !matches!(begin.message, Message::Begin { .. }) {
        exit(73)
    }
    if args[1] == "early-exit" {
        exit(0)
    }
    let send = |message: Message, control: &mut trust_worker_linux::RetainedControl<'_>| {
        let envelope = Envelope { binding: begin.binding.clone(), message };
        let Ok(bytes) = trust_process_isolation::encode(&envelope, &budget) else { exit(73) };
        if control.send(&bytes, &budget).is_err() {
            exit(73)
        }
    };
    if args[1] == "partial" {
        emit(3, &[1]);
        exit(0)
    }
    if args[1] == "wrong-binding" {
        let mut binding = begin.binding.clone();
        binding.unit[0] ^= 1;
        let bytes = trust_process_isolation::encode(
            &Envelope { binding, message: Message::Ready },
            &budget,
        )
        .unwrap_or_else(|_| exit(73));
        emit(3, &bytes);
        exit(0)
    }
    send(Message::Ready, &mut control);
    let mut dispatcher_output = None;
    match args[1].as_str() {
        "stall" => loop {
            std::hint::spin_loop()
        },
        "flood" => loop {
            emit(1, &[b'x'; 4096])
        },
        "failure" => {
            send(Message::Failure { reason: "fixture failure".into() }, &mut control);
            exit(0)
        }
        "callback" => {
            send(
                Message::Call(Call {
                    id: 1,
                    method: Method::InjectedEnvVar,
                    arguments: vec![Value::Text("FIXTURE".into())],
                }),
                &mut control,
            );
            let bytes = control.receive(&budget).unwrap_or_else(|_| exit(73));
            if trust_process_isolation::decode(&bytes, &budget).is_err() {
                exit(73)
            }
        }
        "dispatcher" | "dispatcher-stale" => {
            let Message::Begin { inputs, globals, .. } = &begin.message else { exit(73) };
            let Some(&input) = inputs.first() else { exit(73) };
            let mut invoke = |id, method, arguments| {
                send(Message::Call(Call { id, method, arguments }), &mut control);
                let bytes = control.receive(&budget).unwrap_or_else(|_| exit(73));
                let reply =
                    trust_process_isolation::decode(&bytes, &budget).unwrap_or_else(|_| exit(73));
                if reply.binding != begin.binding {
                    exit(73)
                }
                match reply.message {
                    Message::Reply { id: actual, value } if actual == id => value,
                    _ => exit(73),
                }
            };
            let Value::Stream(copy) = invoke(1, Method::TsClone, vec![Value::Stream(input)]) else {
                exit(73)
            };
            if invoke(2, Method::TsToString, vec![Value::Stream(copy)])
                != Value::Text("alpha beta".into())
                || invoke(3, Method::SpanSourceText, vec![Value::Span(globals[1])])
                    != Value::OptionalText(Some("alpha".into()))
                || invoke(4, Method::TsDrop, vec![Value::Stream(input)]) != Value::Unit
            {
                exit(73)
            }
            if args[1] == "dispatcher-stale" {
                // The real compiler handle table must refuse resurrection of
                // the consumed input; no successful reply should arrive.
                invoke(5, Method::TsToString, vec![Value::Stream(input)]);
                exit(74)
            }
            dispatcher_output = Some(copy);
        }
        "control-closed" | "control-owner" | "control-cancel" | "control-deadline" => {
            let error = match args[1].as_str() {
                "control-closed" => {
                    control.close();
                    control.receive(&budget).unwrap_err()
                }
                "control-owner" => {
                    let other = Budget::new(budget.limits(), budget.deadline())
                        .unwrap_or_else(|_| exit(74));
                    let error = control.receive(&other).unwrap_err();
                    if other.check().is_err() {
                        exit(74)
                    }
                    error
                }
                "control-cancel" => {
                    budget.cancel();
                    control.receive(&budget).unwrap_err()
                }
                _ => control.receive(&budget).unwrap_err(),
            };
            if budget.check().is_ok() || control.receive(&budget) != Err(error) {
                exit(74)
            }
            // Logical refusal must retain FD3. It must never release/recycle it.
            if unsafe { libc::fcntl(3, libc::F_GETFD) } < 0 {
                exit(74)
            }
            emit(1, b"CONTROL-REFUSED\n");
            exit(76)
        }
        "as" => {
            // SAFETY: deliberately oversized anonymous allocation must fail
            // under the launcher's finite kernel AS allowance; never accessed.
            let map = unsafe {
                libc::mmap(
                    std::ptr::null_mut(),
                    512 * 1024 * 1024,
                    libc::PROT_READ | libc::PROT_WRITE,
                    libc::MAP_PRIVATE | libc::MAP_ANONYMOUS,
                    -1,
                    0,
                )
            };
            if map != libc::MAP_FAILED
                || std::io::Error::last_os_error().raw_os_error() != Some(libc::ENOMEM)
            {
                exit(74)
            }
        }
        "positive" | "trailing" | "abnormal" => {}
        _ => exit(70),
    }
    emit(1, b"STATIC-PASS\n");
    let output = if args[1] == "trailing" || args[1] == "abnormal" {
        Some(trust_process_isolation::Handle {
            invocation: begin.binding.invocation,
            slot: 0,
            generation: 1,
            kind: trust_process_isolation::HandleKind::Stream,
        })
    } else {
        dispatcher_output
    };
    send(Message::Finish { output }, &mut control);
    if args[1] == "trailing" {
        emit(3, b"x")
    }
    if args[1] == "abnormal" {
        exit(75)
    }
    control.close();
    drop(control);
    // Successful terminal closure is logical. Kernel teardown supplies EOF;
    // no destructor closes or shuts down the protected endpoint.
    if unsafe { libc::fcntl(3, libc::F_GETFD) } < 0 || budget.check().is_err() {
        exit(74)
    }
    exit(0)
}
