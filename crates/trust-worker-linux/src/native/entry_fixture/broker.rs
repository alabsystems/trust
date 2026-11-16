//! Actual separately executed broker role of the same pinned static helper.
use std::fs::File;
use std::os::fd::AsRawFd;

use trust_process_isolation::Charge;

use super::{fail, signal};
use crate::native::configuration::Decoded;
use crate::native::grant::LocalGrant;
use crate::native::kernel::Service;
use crate::native::mappings::Mappings;
use crate::native::{bootstrap, io, receipt, reserve};

pub(super) fn run(config: Decoded, grant: LocalGrant, transfer: File, parent: i32) -> ! {
    let b = grant.budget.clone();
    let mut task = [0; 4];
    io::read_exact(&mut task, &b).unwrap_or_else(|_| fail(130));
    crate::native::charge(&b, Charge { wire_bytes: 4, ..Charge::default() })
        .unwrap_or_else(|_| fail(130));
    let worker = u32::from_le_bytes(task);
    if worker == 0 || worker == parent as u32 || worker == std::process::id() {
        fail(130)
    }
    bootstrap::configure(&transfer, &b).unwrap_or_else(|_| fail(131));
    signal(b'A', &b);
    loop {
        crate::native::charge(&b, Charge { work: 64, ..Charge::default() })
            .unwrap_or_else(|_| fail(131));
        let mut event = libc::pollfd { fd: transfer.as_raw_fd(), events: libc::POLLIN, revents: 0 };
        // SAFETY: one complete poll record and finite trusted startup wait.
        let n = unsafe { libc::poll(&mut event, 1, 1) };
        if n < 0 {
            fail(131)
        }
        if n > 0 {
            if event.revents != libc::POLLIN {
                fail(131)
            }
            break;
        }
    }
    let handoff = bootstrap::receive_broker(&transfer, parent as u32, worker, grant.capsule, &b)
        .unwrap_or_else(|_| fail(132));
    crate::restriction::validate_broker_handoff(
        worker,
        handoff.memory.as_raw_fd(),
        handoff.maps.as_raw_fd(),
    )
    .unwrap_or_else(|_| fail(132));
    drop(transfer);
    let inventory = config.inventory(&b).unwrap_or_else(|_| fail(133));
    let mut service = Service::adopt(handoff.listener, handoff.memory, worker, inventory)
        .unwrap_or_else(|_| fail(134));
    let mut mappings = Mappings::prepare(handoff.maps, &b).unwrap_or_else(|_| fail(135));
    let retained = service.descriptors(mappings.file()).unwrap_or_else(|_| fail(135));
    let mut issued = reserve(31, &b).unwrap_or_else(|_| fail(135));
    let profile = crate::Profile {
        parent_pid: parent,
        inputs: &config.inputs,
        limits: crate::KernelLimits {
            address_space_bytes: 256 * 1024 * 1024,
            stack_bytes: 8 * 1024 * 1024,
            file_bytes: 1024 * 1024,
            descriptors: 1024,
        },
    };
    crate::restriction::install_broker(
        &profile,
        &b,
        worker,
        service.listener_fd(),
        service.memory_fd(),
        mappings.fd(),
        &retained,
    )
    .unwrap_or_else(|_| fail(136));
    signal(b'B', &b);
    let mut sequence = 0u64;
    let mut retired = false;
    loop {
        crate::native::charge(&b, Charge { work: 64, ..Charge::default() })
            .unwrap_or_else(|_| fail(137));
        let mut events = [
            libc::pollfd {
                fd: if retired { -1 } else { service.listener_fd() },
                events: libc::POLLIN,
                revents: 0,
            },
            libc::pollfd { fd: 3, events: libc::POLLIN, revents: 0 },
        ];
        let timeout = libc::timespec { tv_sec: 0, tv_nsec: 1_000_000 };
        // SAFETY: complete live fixed-role records and finite wait. The opaque
        // kernel service stays in this owned child, never the parent/monitor.
        if unsafe {
            libc::ppoll(
                events.as_mut_ptr(),
                events.len() as libc::nfds_t,
                &timeout,
                std::ptr::null(),
            )
        } < 0
        {
            fail(137)
        }
        if events[0].revents & !(libc::POLLIN | libc::POLLHUP) != 0
            || events[1].revents & !libc::POLLIN != 0
        {
            fail(137)
        }
        if events[0].revents & libc::POLLHUP != 0 {
            // Target exit retires service; it is neither broker success nor
            // parent completion authority. Stay owned/alive until the monitor
            // independently validates terminal protocol/zero exit or refuses.
            // Exiting here races legitimate worker EOF and wrongly cancels it.
            retired = true;
        }
        if !retired && events[0].revents == libc::POLLIN {
            if issued.len() == 31 {
                fail(138)
            }
            issued.push(service.ready_once().unwrap_or_else(|_| fail(138)));
        }
        if events[1].revents == libc::POLLIN {
            if retired {
                fail(139)
            }
            if io::byte(&b).unwrap_or_else(|_| fail(139)) != b'M' {
                fail(139)
            }
            crate::native::charge(&b, Charge { calls: 1, ..Charge::default() })
                .unwrap_or_else(|_| fail(139));
            sequence = sequence.checked_add(1).unwrap_or_else(|| fail(139));
            let page = mappings.page();
            let observed = mappings.observe(&issued).unwrap_or_else(|_| fail(140));
            receipt::send(
                &grant,
                config.graph.unwrap_or_else(|| fail(140)),
                &config.binding,
                sequence,
                page,
                &issued,
                observed,
            )
            .unwrap_or_else(|_| fail(141));
        }
    }
}
