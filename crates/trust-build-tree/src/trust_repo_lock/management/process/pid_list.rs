//! Public Darwin PID-list observations; these DATA rows grant no ownership.
use std::io;

use super::invalid;

pub(super) fn list_selected_pids(
    selector: u32,
    argument: u32,
    require_observer: bool,
) -> io::Result<Vec<u32>> {
    let initial = read_pid_bytes(selector, argument, None)?;
    let mut capacity = (initial / std::mem::size_of::<i32>()).saturating_add(128);
    for _ in 0..4 {
        if capacity > 1_000_000 {
            return Err(invalid("native process table exceeds its bound"));
        }
        let mut pids = vec![0_i32; capacity];
        let count = read_pid_bytes(selector, argument, Some(&mut pids))?;
        if !count.is_multiple_of(std::mem::size_of::<i32>()) {
            return Err(invalid("incomplete native PID element"));
        }
        let count = count / std::mem::size_of::<i32>();
        if count >= capacity {
            capacity = capacity.saturating_mul(2);
            continue;
        }
        pids.truncate(count);
        let pids: Vec<u32> =
            pids.into_iter().filter(|pid| *pid > 0).map(|pid| pid as u32).collect();
        if require_observer && !pids.contains(&std::process::id()) {
            return Err(invalid("native account process table omitted the observer"));
        }
        return Ok(pids);
    }
    Err(invalid("native process table did not settle within its observation bound"))
}

// Apple libproc maps __proc_info failure to zero while preserving errno.
// Zero is also a valid empty selection. Inspect only this calling thread's
// errno, immediately around the public call; never turn a failed census into
// an empty population. Both the sizing and population calls use this owner.
fn read_pid_bytes(selector: u32, argument: u32, output: Option<&mut [i32]>) -> io::Result<usize> {
    let (buffer, bytes) = match output {
        None => (std::ptr::null_mut(), 0),
        Some(output) => (
            output.as_mut_ptr().cast(),
            i32::try_from(std::mem::size_of_val(output))
                .map_err(|_| invalid("native PID buffer exceeds its bound"))?,
        ),
    };
    #[cfg(test)]
    let injected = FAULT.with(|fault| {
        let mut fault = fault.borrow_mut();
        match fault.as_mut() {
            Some(fault) if fault.skip > 0 => {
                fault.skip -= 1;
                None
            }
            Some(fault) if fault.remaining > 0 => {
                fault.remaining -= 1;
                Some((fault.count, fault.errno))
            }
            _ => None,
        }
    });
    // SAFETY: __error is Darwin's calling-thread errno location. No descriptor,
    // OFD flags, source cursor or other thread's errno is changed. All buffer
    // selection and test-fault setup above precede this native bookend.
    let errno = unsafe { libc::__error() };
    unsafe {
        *errno = 0;
    }
    #[cfg(test)]
    let count = match injected {
        Some((count, injected_errno)) => {
            unsafe {
                *errno = injected_errno;
            }
            count
        }
        None => unsafe { libc::proc_listpids(selector, argument, buffer, bytes) },
    };
    #[cfg(not(test))]
    // SAFETY: null/zero sizing or our live writable slice for exactly bytes;
    // the public libproc function does not retain the buffer.
    let count = unsafe { libc::proc_listpids(selector, argument, buffer, bytes) };
    let observed_errno = unsafe { *errno };
    if count < 0 || count == 0 && observed_errno != 0 {
        return Err(if observed_errno == 0 {
            invalid("native PID census failed without errno")
        } else {
            io::Error::from_raw_os_error(observed_errno)
        });
    }
    Ok(count as usize)
}

#[cfg(test)]
#[derive(Clone, Copy)]
struct ListFault {
    skip: usize,
    remaining: usize,
    count: i32,
    errno: i32,
}
#[cfg(test)]
thread_local! {
    static FAULT: std::cell::RefCell<Option<ListFault>> = const { std::cell::RefCell::new(None) };
}
#[cfg(test)]
struct FaultGuard(Option<ListFault>, std::marker::PhantomData<std::rc::Rc<()>>);
#[cfg(test)]
impl FaultGuard {
    fn install(skip: usize, remaining: usize, count: i32, errno: i32) -> Self {
        Self(
            FAULT.with(|fault| fault.replace(Some(ListFault { skip, remaining, count, errno }))),
            std::marker::PhantomData,
        )
    }
}
#[cfg(test)]
impl Drop for FaultGuard {
    fn drop(&mut self) {
        FAULT.with(|fault| {
            fault.replace(self.0.take());
        });
    }
}

#[cfg(test)]
mod tests;
