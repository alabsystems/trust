// Trust: Regression test for rust-lang#126600
// Verifies that concurrent calls to process::exit() do not cause undefined
// behavior from racing in C runtime cleanup (atexit handlers, stdio flushing).
// The fix uses an atomic flag (unique_thread_exit) so only one thread ever
// calls libc::exit; other threads park indefinitely.
//
//@ run-pass
//@ ignore-emscripten no threads
//@ ignore-sgx no processes

// Copyright 2026 Andrew Yates <andrewyates.name@gmail.com>

use std::process;
use std::thread;

fn main() {
    // Spawn multiple threads that all attempt to exit simultaneously.
    // Without the fix, this would be undefined behavior on glibc/macOS/BSD
    // due to concurrent libc::exit calls racing on atexit handler execution.
    //
    // With the fix, exactly one thread wins the atomic compare_exchange in
    // unique_thread_exit() and proceeds to exit. All other threads park
    // forever (which is fine because the process is about to terminate).
    //
    // We use exit code 0 so the test harness sees success.
    let mut handles = Vec::new();
    for _ in 0..4 {
        handles.push(thread::spawn(|| {
            process::exit(0);
        }));
    }

    // Also call exit from the main thread to race with spawned threads.
    process::exit(0);
}
