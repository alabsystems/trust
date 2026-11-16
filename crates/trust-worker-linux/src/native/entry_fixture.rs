//! Pinned static native runtime diagnostic. The real worker and broker roles
//! exercise confinement/DSO loading; no Rust Client ABI or macro admission.
use std::fs::File;
use std::os::fd::{AsRawFd, BorrowedFd, FromRawFd};
use std::sync::atomic::{AtomicU64, Ordering};

use trust_process_isolation::{Charge, Envelope, Message, Transport};

use super::{bootstrap, configuration, grant, io};

mod broker;

static OBSERVED: AtomicU64 = AtomicU64::new(123);
fn exit(code: i32) -> ! {
    // SAFETY: terminal exit avoids forbidden descriptor destructors and late
    // untrusted DSO destructors after terminal protocol/receipt validation.
    unsafe { libc::_exit(code) }
}
fn fail(stage: u8) -> ! {
    // SAFETY: one fixed stage byte to the declared diagnostic output pipe.
    unsafe { libc::write(2, (&stage as *const u8).cast(), 1) };
    exit(stage as i32)
}
fn emit(bytes: &[u8]) {
    // SAFETY: initialized bounded startup bytes on authenticated fixed FD3.
    if unsafe { libc::write(3, bytes.as_ptr().cast(), bytes.len()) } != bytes.len() as isize {
        fail(100)
    }
}
fn signal(byte: u8, b: &trust_process_isolation::Budget) {
    super::charge(b, Charge { wire_bytes: 1, ..Charge::default() }).unwrap_or_else(|_| fail(101));
    io::write_all(&[byte], b).unwrap_or_else(|_| fail(101));
}

pub fn entry_fixture() -> ! {
    let args: Vec<_> = std::env::args().collect();
    if args.len() != 3 || std::env::vars_os().next().is_some() {
        fail(103)
    }
    let Ok(transfer_fd) = args[2].parse::<i32>() else { fail(103) };
    // SAFETY: direct parent observation. Birth already armed PDEATHSIG.
    let parent = unsafe { libc::getppid() };
    crate::restriction::authenticate_bootstrap(transfer_fd, parent).unwrap_or_else(|_| fail(104));
    // SAFETY: authenticated live high inherited socket, no previous File owner
    // exists in this fresh trusted executable. Dense input roles start at5.
    let transfer = unsafe { File::from_raw_fd(transfer_fd) };
    emit(&(&OBSERVED as *const AtomicU64 as u64).to_le_bytes());
    let role = if args[1] == "broker" || args[1] == "standby" {
        grant::Role::Broker
    } else {
        grant::Role::Worker
    };
    let raw = io::startup().unwrap_or_else(|_| fail(105));
    let delegated = grant::LocalGrant::adopt(&raw, role).unwrap_or_else(|_| fail(106));
    let b = delegated.budget.clone();
    let begin = configuration::begin(&b).unwrap_or_else(|_| fail(107));
    delegated.bind(&begin.binding).unwrap_or_else(|_| fail(108));
    let config =
        configuration::Decoded::receive(begin.binding.clone(), &b).unwrap_or_else(|_| fail(109));
    match args[1].as_str() {
        "broker" => broker::run(config, delegated, transfer, parent),
        "standby" => {
            if io::byte(&b).unwrap_or_else(|_| fail(110)) != b'E' {
                fail(110)
            }
            exit(0)
        }
        "early-exit" => exit(0),
        "entry" | "bad-transfer" | "load" => {}
        _ => fail(110),
    }
    let alias = if args[1] == "load" {
        Some(config.root_alias(&b).unwrap_or_else(|_| fail(111)))
    } else {
        None
    };
    let profile = crate::Profile {
        parent_pid: parent,
        inputs: &config.inputs,
        limits: crate::KernelLimits {
            address_space_bytes: 256 * 1024 * 1024,
            stack_bytes: 8 * 1024 * 1024,
            file_bytes: 1024 * 1024,
            descriptors: 64,
        },
    };
    if args[1] == "bad-transfer" {
        // SAFETY: controlled negative substitution before actual native entry.
        if unsafe { libc::dup2(0, transfer_fd) } != transfer_fd {
            fail(112)
        }
    }
    // SAFETY: live inherited slot remains uniquely owned throughout trusted
    // entry; no constructor, thread, signal handler or mutator has run.
    let borrowed = unsafe { BorrowedFd::borrow_raw(transfer_fd) };
    let mut installed =
        crate::restriction::install_native(&profile, &b, borrowed).unwrap_or_else(|_| {
            emit(b"R");
            exit(117)
        });
    if installed.listener.as_raw_fd() != 5 + config.inputs.len() as i32
        || installed.restrictions.landlock_abi() < 3
    {
        fail(113)
    }
    OBSERVED.store(456, Ordering::Relaxed);
    let listener: File = installed.listener.into();
    bootstrap::send_listener(&transfer, &listener, &b).unwrap_or_else(|_| fail(114));
    drop(listener);
    drop(transfer);
    signal(b'I', &b);
    if let Some(alias) = alias {
        if io::byte(&b).unwrap_or_else(|_| fail(115)) != b'L' {
            fail(115)
        }
        // SAFETY: the terminated literal owner alias is served exclusively by
        // the immutable broker. The actual native filter precedes this call,
        // including every relocation and untrusted constructor it invokes.
        let library =
            unsafe { libc::dlopen(alias.as_ptr().cast(), libc::RTLD_NOW | libc::RTLD_LOCAL) };
        if library.is_null() {
            fail(116)
        }
        // SAFETY: this qualified C diagnostic symbol has the declared ABI.
        // Arbitrary native corruption/crash remains confined to this worker;
        // this does not qualify Rust's native Client/declaration ABI.
        let symbol = unsafe { libc::dlsym(library, c"trust_native_fixture".as_ptr()) };
        if symbol.is_null() {
            fail(118)
        }
        signal(b'Q', &b);
        if io::byte(&b).unwrap_or_else(|_| fail(119)) != b'G' {
            fail(119)
        }
        let mut control = installed.restrictions.control().unwrap_or_else(|_| fail(120));
        let ready = trust_process_isolation::encode(
            &Envelope { binding: begin.binding.clone(), message: Message::Ready },
            &b,
        )
        .unwrap_or_else(|_| fail(120));
        control.send(&ready, &b).unwrap_or_else(|_| fail(120));
        // SAFETY: known C qualification fixture entry, in the untrusted worker.
        let function: unsafe extern "C" fn() -> i32 = unsafe { std::mem::transmute(symbol) };
        if unsafe { function() } != 7 {
            fail(121)
        }
        // SAFETY: bounded diagnostic result to write-only output capability.
        if unsafe { libc::write(1, [7u8].as_ptr().cast(), 1) } != 1 {
            fail(121)
        }
        let finish = trust_process_isolation::encode(
            &Envelope { binding: begin.binding, message: Message::Finish { output: None } },
            &b,
        )
        .unwrap_or_else(|_| fail(122));
        control.send(&finish, &b).unwrap_or_else(|_| fail(122));
        control.close();
        drop(control);
    }
    // Native lifecycle acknowledgement follows terminal B1; it does not reopen
    // B1 or reset any allowance. Only actual process exit supplies final EOF.
    if io::byte(&b).unwrap_or_else(|_| fail(123)) != b'E' {
        fail(123)
    }
    exit(0)
}
