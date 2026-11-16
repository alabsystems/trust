//! dispatch-cost probe (docs/STATUS.md "Dispatch cost").
//!
//! Measures the fixed cost of handing one kernel to the GPU and getting its
//! result back on Apple silicon unified memory. The kernel does one store into
//! a shared buffer, so each sample is checked: the store's value must be
//! visible to the CPU, with no copy, when the wait returns. Every sample is
//! printed; `scripts/dispatch_cost.py` owns the statistics.
//!
//! Three series. `hot`: dispatches back to back. `idle<ms>`: the thread sleeps
//! for the gap, so the CPU core and the GPU both go idle. `spin<ms>`: the
//! thread spins for the gap, so only the GPU goes idle. The difference between
//! the last two is what the sleeping thread costs, not the device.
//!
//! This package has no dependencies. It is built with `targo --unverified`: it talks to
//! Metal through the Objective-C runtime, the calls a Rust dispatch shim would
//! make. It is a measurement, not that shim, and grants no proof authority.

use std::ffi::{CStr, CString, c_char, c_void};

type Id = *mut c_void;
type Sel = *const c_void;

#[repr(C)]
struct MtlSize {
    width: usize,
    height: usize,
    depth: usize,
}

#[link(name = "objc")]
unsafe extern "C" {
    fn objc_getClass(name: *const c_char) -> Id;
    fn sel_registerName(name: *const c_char) -> Sel;
    fn objc_msgSend();
    fn objc_autoreleasePoolPush() -> *mut c_void;
    fn objc_autoreleasePoolPop(pool: *mut c_void);
}

#[link(name = "Foundation", kind = "framework")]
unsafe extern "C" {}

// A command-line program gets a default device only with CoreGraphics linked.
#[link(name = "CoreGraphics", kind = "framework")]
unsafe extern "C" {}

#[link(name = "Metal", kind = "framework")]
unsafe extern "C" {
    fn MTLCreateSystemDefaultDevice() -> Id;
}

unsafe extern "C" {
    fn clock_gettime_nsec_np(clock: u32) -> u64;
    fn pthread_set_qos_class_self_np(qos: u32, relative_priority: i32) -> i32;
}

const CLOCK_UPTIME_RAW: u32 = 8;
const QOS_CLASS_USER_INTERACTIVE: u32 = 0x21;
const MTL_RESOURCE_STORAGE_MODE_SHARED: usize = 0;
const MTL_COMMAND_BUFFER_STATUS_COMPLETED: usize = 4;

const KERNEL: &str = "#include <metal_stdlib>\n\
using namespace metal;\n\
kernel void k(device uint *out [[buffer(0)]], constant uint &i [[buffer(1)]]) {\n\
    out[0] = i;\n\
}\n";

fn sel(name: &CStr) -> Sel {
    // SAFETY: `name` is a NUL-terminated string that outlives the call.
    unsafe { sel_registerName(name.as_ptr()) }
}

/// Sends one Objective-C message. The caller states the exact C signature of
/// the method: `objc_msgSend` is a trampoline and must be called at the type
/// of the method it reaches. A literal name is looked up on the spot; the
/// timed loop passes selectors `Selectors` looked up once.
macro_rules! msg {
    ($ret:ty; $obj:expr, $name:literal $(, $arg:expr => $ty:ty)*) => {
        msg!($ret; $obj, sel($name) $(, $arg => $ty)*)
    };
    ($ret:ty; $obj:expr, $sel:expr $(, $arg:expr => $ty:ty)*) => {{
        let f: unsafe extern "C" fn(Id, Sel $(, $ty)*) -> $ret =
            // SAFETY: a function pointer cast between `extern "C"` types.
            unsafe { std::mem::transmute(objc_msgSend as unsafe extern "C" fn()) };
        // SAFETY: the caller named the method's signature and `$obj` is a
        // live object that responds to it.
        unsafe { f($obj, $sel $(, $arg)*) }
    }};
}

/// Every selector a dispatch sends, looked up before the first sample: a
/// dispatch allocates nothing and looks nothing up.
struct Selectors {
    command_buffer: Sel,
    compute_command_encoder: Sel,
    set_compute_pipeline_state: Sel,
    set_buffer: Sel,
    set_bytes: Sel,
    dispatch_threadgroups: Sel,
    end_encoding: Sel,
    commit: Sel,
    wait_until_completed: Sel,
    status: Sel,
    gpu_start_time: Sel,
    gpu_end_time: Sel,
}

impl Selectors {
    fn new() -> Self {
        Selectors {
            command_buffer: sel(c"commandBuffer"),
            compute_command_encoder: sel(c"computeCommandEncoder"),
            set_compute_pipeline_state: sel(c"setComputePipelineState:"),
            set_buffer: sel(c"setBuffer:offset:atIndex:"),
            set_bytes: sel(c"setBytes:length:atIndex:"),
            dispatch_threadgroups: sel(c"dispatchThreadgroups:threadsPerThreadgroup:"),
            end_encoding: sel(c"endEncoding"),
            commit: sel(c"commit"),
            wait_until_completed: sel(c"waitUntilCompleted"),
            status: sel(c"status"),
            gpu_start_time: sel(c"GPUStartTime"),
            gpu_end_time: sel(c"GPUEndTime"),
        }
    }
}

fn now() -> u64 {
    // SAFETY: no pointers; the raw uptime clock always exists on Darwin.
    unsafe { clock_gettime_nsec_np(CLOCK_UPTIME_RAW) }
}

fn ns_string(text: &str) -> Id {
    let text = CString::new(text).expect("text has no NUL");
    // SAFETY: NSString exists once Foundation is linked.
    let class = unsafe { objc_getClass(c"NSString".as_ptr()) };
    msg!(Id; class, c"stringWithUTF8String:", text.as_ptr() => *const c_char)
}

fn rust_string(ns: Id) -> String {
    if ns.is_null() {
        return String::from("-");
    }
    let bytes = msg!(*const c_char; ns, c"UTF8String");
    if bytes.is_null() {
        return String::from("-");
    }
    // SAFETY: `UTF8String` returns a NUL-terminated buffer that lives as long
    // as the enclosing autorelease pool.
    unsafe { CStr::from_ptr(bytes) }.to_string_lossy().into_owned()
}

fn fail(what: &str, error: Id) -> ! {
    let detail = if error.is_null() {
        String::new()
    } else {
        format!(": {}", rust_string(msg!(Id; error, c"localizedDescription")))
    };
    eprintln!("dispatch-cost probe: {what}{detail}");
    std::process::exit(1)
}

struct Gpu {
    sels: Selectors,
    queue: Id,
    pipeline: Id,
    buffer: Id,
    cell: *mut u32,
}

struct Sample {
    /// Call to return, with the call's Metal objects released.
    call_ns: u64,
    /// Call until the kernel's store is visible to the CPU.
    visible_ns: u64,
    /// The GPU's own start-to-end time for the command buffer.
    gpu_ns: u64,
}

impl Gpu {
    fn dispatch(&self, token: u32) -> Sample {
        let one = || MtlSize { width: 1, height: 1, depth: 1 };
        let start = now();
        // SAFETY: pushes a pool that the matching pop below releases.
        let pool = unsafe { objc_autoreleasePoolPush() };
        let sels = &self.sels;
        let commands = msg!(Id; self.queue, sels.command_buffer);
        let encoder = msg!(Id; commands, sels.compute_command_encoder);
        msg!((); encoder, sels.set_compute_pipeline_state, self.pipeline => Id);
        msg!((); encoder, sels.set_buffer, self.buffer => Id, 0 => usize, 0 => usize);
        msg!((); encoder, sels.set_bytes,
            (&raw const token).cast() => *const c_void, 4 => usize, 1 => usize);
        msg!((); encoder, sels.dispatch_threadgroups, one() => MtlSize, one() => MtlSize);
        msg!((); encoder, sels.end_encoding);
        msg!((); commands, sels.commit);
        msg!((); commands, sels.wait_until_completed);
        // SAFETY: `cell` is the shared buffer's CPU address, four bytes long,
        // and the GPU finished writing it before the wait returned.
        let seen = unsafe { self.cell.read_volatile() };
        let visible = now();
        let status = msg!(usize; commands, sels.status);
        if status != MTL_COMMAND_BUFFER_STATUS_COMPLETED {
            fail("a command buffer did not complete", msg!(Id; commands, c"error"));
        }
        if seen != token {
            eprintln!("dispatch-cost probe: the kernel stored {seen}, expected {token}");
            std::process::exit(1);
        }
        let gpu_start = msg!(f64; commands, sels.gpu_start_time);
        let gpu_end = msg!(f64; commands, sels.gpu_end_time);
        // SAFETY: `pool` came from the push above and nothing below uses an
        // object it owns.
        unsafe { objc_autoreleasePoolPop(pool) };
        let end = now();
        Sample {
            call_ns: end - start,
            visible_ns: visible - start,
            gpu_ns: ((gpu_end - gpu_start).max(0.0) * 1e9) as u64,
        }
    }
}

fn setup() -> (Gpu, String, bool) {
    // SAFETY: returns a retained device or null.
    let device = unsafe { MTLCreateSystemDefaultDevice() };
    if device.is_null() {
        fail("this machine has no Metal device", std::ptr::null_mut());
    }
    let name = rust_string(msg!(Id; device, c"name"));
    let unified = msg!(bool; device, c"hasUnifiedMemory");

    let mut error: Id = std::ptr::null_mut();
    let library = msg!(Id; device, c"newLibraryWithSource:options:error:",
        ns_string(KERNEL) => Id, std::ptr::null_mut() => Id, &raw mut error => *mut Id);
    if library.is_null() {
        fail("the kernel did not compile", error);
    }
    let function = msg!(Id; library, c"newFunctionWithName:", ns_string("k") => Id);
    if function.is_null() {
        fail("the library has no function `k`", std::ptr::null_mut());
    }
    let pipeline = msg!(Id; device, c"newComputePipelineStateWithFunction:error:",
        function => Id, &raw mut error => *mut Id);
    if pipeline.is_null() {
        fail("the pipeline was not built", error);
    }
    let queue = msg!(Id; device, c"newCommandQueue");
    let buffer = msg!(Id; device, c"newBufferWithLength:options:",
        4 => usize, MTL_RESOURCE_STORAGE_MODE_SHARED => usize);
    if queue.is_null() || buffer.is_null() {
        fail("no command queue or shared buffer", std::ptr::null_mut());
    }
    let cell = msg!(*mut c_void; buffer, c"contents").cast::<u32>();
    if cell.is_null() {
        fail("the shared buffer has no CPU address", std::ptr::null_mut());
    }
    (Gpu { sels: Selectors::new(), queue, pipeline, buffer, cell }, name, unified)
}

struct Plan {
    warm: u32,
    hot: u32,
    idle_ms: Vec<u64>,
    idle_reps: u32,
    spin: bool,
}

fn plan() -> Plan {
    let mut plan =
        Plan { warm: 2000, hot: 20000, idle_ms: vec![1, 10, 100, 1000], idle_reps: 50, spin: true };
    let mut args = std::env::args().skip(1);
    let usage = || -> ! {
        eprintln!(
            "usage: dispatch-cost-probe [--warm N] [--hot N] [--idle-ms A,B,..] [--idle-reps N] \
             [--spin 0|1]"
        );
        std::process::exit(2)
    };
    while let Some(flag) = args.next() {
        let Some(value) = args.next() else { usage() };
        match flag.as_str() {
            "--warm" => plan.warm = value.parse().unwrap_or_else(|_| usage()),
            "--hot" => plan.hot = value.parse().unwrap_or_else(|_| usage()),
            "--idle-reps" => plan.idle_reps = value.parse().unwrap_or_else(|_| usage()),
            "--spin" => {
                plan.spin = match value.as_str() {
                    "0" => false,
                    "1" => true,
                    _ => usage(),
                }
            }
            "--idle-ms" => {
                plan.idle_ms = value
                    .split(',')
                    .filter(|part| !part.is_empty())
                    .map(|part| part.parse().unwrap_or_else(|_| usage()))
                    .collect();
            }
            _ => usage(),
        }
    }
    plan
}

fn main() {
    use std::io::Write;

    let plan = plan();
    // SAFETY: sets this thread's scheduling class; no pointers.
    let qos = unsafe { pthread_set_qos_class_self_np(QOS_CLASS_USER_INTERACTIVE, 0) };
    // SAFETY: the pool is popped at the end of `main`.
    let pool = unsafe { objc_autoreleasePoolPush() };
    let (gpu, name, unified) = setup();

    let mut token: u32 = 0;
    let mut next = || {
        token = token.wrapping_add(1);
        token
    };
    let mut hot = Vec::with_capacity(plan.hot as usize);
    for _ in 0..plan.warm {
        gpu.dispatch(next());
    }
    for _ in 0..plan.hot {
        hot.push(gpu.dispatch(next()));
    }
    let mut idle = Vec::new();
    for &gap in &plan.idle_ms {
        for _ in 0..plan.idle_reps {
            std::thread::sleep(std::time::Duration::from_millis(gap));
            idle.push(("idle", gap, gpu.dispatch(next())));
        }
    }
    if plan.spin {
        for &gap in &plan.idle_ms {
            for _ in 0..plan.idle_reps {
                let until = now() + gap * 1_000_000;
                while now() < until {
                    std::hint::spin_loop();
                }
                idle.push(("spin", gap, gpu.dispatch(next())));
            }
        }
    }

    // Nothing is printed while a sample is being taken.
    let out = std::io::stdout();
    let mut out = std::io::BufWriter::new(out.lock());
    let mut line = |text: String| writeln!(out, "{text}").expect("stdout is writable");
    let row = |series: &str, sample: &Sample| {
        format!("S {series} {} {} {}", sample.call_ns, sample.visible_ns, sample.gpu_ns)
    };
    line(format!("device {name}"));
    line(format!("unified {}", u8::from(unified)));
    line(format!("qos {}", if qos == 0 { "user-interactive" } else { "default" }));
    line(format!("warm {}", plan.warm));
    for sample in &hot {
        line(row("hot", sample));
    }
    for (kind, gap, sample) in &idle {
        line(row(&format!("{kind}{gap}"), sample));
    }
    drop(line);
    out.flush().expect("stdout is writable");
    // SAFETY: `pool` came from the push at the top of `main`.
    unsafe { objc_autoreleasePoolPop(pool) };
}
