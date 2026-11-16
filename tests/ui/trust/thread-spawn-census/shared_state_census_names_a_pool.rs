//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=off -Ztrust-send-census -A warnings
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//! Two workers drain one channel through one handler. The thread that runs a
//! consumer is not named for what it shares with it, but two such threads
//! share with EACH OTHER every cell the handler reaches: here a `static mut`
//! both write with no lock held (the receiver's guard is dropped before the
//! handler runs). Once, no note named `LAST` or either worker.

use std::sync::atomic::{AtomicU32, Ordering};
use std::sync::mpsc::{Receiver, channel};
use std::sync::{Arc, Mutex};

static DONE: AtomicU32 = AtomicU32::new(0);
static mut LAST: u32 = 0;

enum Job {
    Work(u32),
    Stop,
}

fn handle(job: Job) -> bool {
    match job {
        Job::Work(n) => {
            DONE.fetch_add(n, Ordering::Relaxed);
            unsafe {
                LAST = n;
            }
            true
        }
        Job::Stop => false,
    }
}

fn worker(rx: Arc<Mutex<Receiver<Job>>>) {
    loop {
        let job = rx.lock().unwrap().recv();
        match job {
            Ok(job) => {
                if !handle(job) {
                    break;
                }
            }
            Err(_) => break,
        }
    }
}

fn main() { //~ NOTE shared-state census: this thread and the consumer `handle` both reach the atomic static `DONE`
    let (tx, rx) = channel::<Job>();
    let rx = Arc::new(Mutex::new(rx));
    let first = {
        let rx = rx.clone();
        std::thread::spawn(move || worker(rx)) //~ NOTE shared-state census: this thread and the consumer `handle` both reach the unsynchronized (`static mut`) static `LAST`; the atomic static `DONE` (it is one of 2 threads that run the consumer: they share these with each other). So do 1 other thread(s): `main::{closure#1}`
    };
    let second = {
        let rx = rx.clone();
        std::thread::spawn(move || worker(rx))
    };
    for n in 0..10 {
        tx.send(Job::Work(n)).unwrap();
    }
    tx.send(Job::Stop).unwrap();
    tx.send(Job::Stop).unwrap();
    first.join().unwrap();
    second.join().unwrap();
    let _ = DONE.load(Ordering::Relaxed);
}
