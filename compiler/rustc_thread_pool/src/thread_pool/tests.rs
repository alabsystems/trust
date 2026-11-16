#![cfg(test)]

use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::mpsc::channel;
use std::sync::{Arc, Mutex};

use crate::{Scope, ScopeFifo, ThreadPool, ThreadPoolBuilder, join};

#[test]
#[should_panic(expected = "Hello, world!")]
fn panic_propagate() {
    let thread_pool = ThreadPoolBuilder::new().build().unwrap();
    thread_pool.install(|| {
        panic!("Hello, world!");
    });
}

#[test]
#[cfg_attr(any(target_os = "emscripten", target_family = "wasm"), ignore)]
fn workers_stop() {
    let registry;

    {
        // once we exit this block, thread-pool will be dropped
        let thread_pool = ThreadPoolBuilder::new().num_threads(22).build().unwrap();
        registry = thread_pool.install(|| {
            // do some work on these threads
            join_a_lot(22);

            Arc::clone(&thread_pool.registry)
        });
        assert_eq!(registry.num_threads(), 22);
    }

    // once thread-pool is dropped, registry should terminate, which
    // should lead to worker threads stopping
    registry.wait_until_stopped();
}

fn join_a_lot(n: usize) {
    if n > 0 {
        join(|| join_a_lot(n - 1), || join_a_lot(n - 1));
    }
}

#[test]
#[cfg_attr(any(target_os = "emscripten", target_family = "wasm"), ignore)]
fn sleeper_stop() {
    use std::{thread, time};

    let registry;

    {
        // once we exit this block, thread-pool will be dropped
        let thread_pool = ThreadPoolBuilder::new().num_threads(22).build().unwrap();
        registry = Arc::clone(&thread_pool.registry);

        // Give time for at least some of the thread pool to fall asleep.
        thread::sleep(time::Duration::from_secs(1));
    }

    // once thread-pool is dropped, registry should terminate, which
    // should lead to worker threads stopping
    registry.wait_until_stopped();
}

/// Creates a start/exit handler that increments an atomic counter.
fn count_handler() -> (Arc<AtomicUsize>, impl Fn(usize)) {
    let count = Arc::new(AtomicUsize::new(0));
    (Arc::clone(&count), move |_| {
        count.fetch_add(1, Ordering::SeqCst);
    })
}

/// Wait until a counter is no longer shared, then return its value.
fn wait_for_counter(mut counter: Arc<AtomicUsize>) -> usize {
    use std::{thread, time};

    for _ in 0..60 {
        counter = match Arc::try_unwrap(counter) {
            Ok(counter) => return counter.into_inner(),
            Err(counter) => {
                thread::sleep(time::Duration::from_secs(1));
                counter
            }
        };
    }

    // That's too long!
    panic!("Counter is still shared!");
}

#[test]
#[cfg_attr(any(target_os = "emscripten", target_family = "wasm"), ignore)]
fn failed_thread_stack() {
    // Note: we first tried to force failure with a `usize::MAX` stack, but
    // macOS and Windows weren't fazed, or at least didn't fail the way we want.
    // They work with `isize::MAX`, but 32-bit platforms may feasibly allocate a
    // 2GB stack, so it might not fail until the second thread.
    let stack_size = isize::MAX as usize;

    let (start_count, start_handler) = count_handler();
    let (exit_count, exit_handler) = count_handler();
    let builder = ThreadPoolBuilder::new()
        .num_threads(10)
        .stack_size(stack_size)
        .start_handler(start_handler)
        .exit_handler(exit_handler);

    let pool = builder.build();
    assert!(pool.is_err(), "thread stack should have failed!");

    // With such a huge stack, 64-bit will probably fail on the first thread;
    // 32-bit might manage the first 2GB, but certainly fail the second.
    let start_count = wait_for_counter(start_count);
    assert!(start_count <= 1);
    assert_eq!(start_count, wait_for_counter(exit_count));
}

#[test]
#[cfg_attr(not(panic = "unwind"), ignore)]
fn panic_thread_name() {
    let (start_count, start_handler) = count_handler();
    let (exit_count, exit_handler) = count_handler();
    let builder = ThreadPoolBuilder::new()
        .num_threads(10)
        .start_handler(start_handler)
        .exit_handler(exit_handler)
        .thread_name(|i| {
            if i >= 5 {
                panic!();
            }
            format!("panic_thread_name#{}", i)
        });

    let pool = crate::unwind::halt_unwinding(|| builder.build());
    assert!(pool.is_err(), "thread-name panic should propagate!");

    // Assuming they're created in order, threads 0 through 4 should have
    // been started already, and then terminated by the panic.
    assert_eq!(5, wait_for_counter(start_count));
    assert_eq!(5, wait_for_counter(exit_count));
}

#[test]
#[cfg_attr(any(target_os = "emscripten", target_family = "wasm"), ignore)]
fn self_install() {
    let pool = ThreadPoolBuilder::new().num_threads(1).build().unwrap();

    // If the inner `install` blocks, then nothing will actually run it!
    assert!(pool.install(|| pool.install(|| true)));
}

// FIXME: We should fix or remove this ignored test.
#[test]
#[ignore]
#[cfg_attr(any(target_os = "emscripten", target_family = "wasm"), ignore)]
fn mutual_install() {
    let pool1 = ThreadPoolBuilder::new().num_threads(1).build().unwrap();
    let pool2 = ThreadPoolBuilder::new().num_threads(1).build().unwrap();

    let ok = pool1.install(|| {
        // This creates a dependency from `pool1` -> `pool2`
        pool2.install(|| {
            // This creates a dependency from `pool2` -> `pool1`
            pool1.install(|| {
                // If they blocked on inter-pool installs, there would be no
                // threads left to run this!
                true
            })
        })
    });
    assert!(ok);
}

// FIXME: We should fix or remove this ignored test.
#[test]
#[ignore]
#[cfg_attr(any(target_os = "emscripten", target_family = "wasm"), ignore)]
fn mutual_install_sleepy() {
    use std::{thread, time};

    let pool1 = ThreadPoolBuilder::new().num_threads(1).build().unwrap();
    let pool2 = ThreadPoolBuilder::new().num_threads(1).build().unwrap();

    let ok = pool1.install(|| {
        // This creates a dependency from `pool1` -> `pool2`
        pool2.install(|| {
            // Give `pool1` time to fall asleep.
            thread::sleep(time::Duration::from_secs(1));

            // This creates a dependency from `pool2` -> `pool1`
            pool1.install(|| {
                // Give `pool2` time to fall asleep.
                thread::sleep(time::Duration::from_secs(1));

                // If they blocked on inter-pool installs, there would be no
                // threads left to run this!
                true
            })
        })
    });
    assert!(ok);
}

#[test]
#[allow(deprecated)]
#[cfg_attr(any(target_os = "emscripten", target_family = "wasm"), ignore)]
fn check_thread_pool_new() {
    let pool = ThreadPool::new(crate::Configuration::new().num_threads(22)).unwrap();
    assert_eq!(pool.current_num_threads(), 22);
}

macro_rules! test_scope_order {
    ($scope:ident => $spawn:ident) => {{
        let builder = ThreadPoolBuilder::new().num_threads(1);
        let pool = builder.build().unwrap();
        pool.install(|| {
            let vec = Mutex::new(vec![]);
            pool.$scope(|scope| {
                let vec = &vec;
                for i in 0..10 {
                    scope.$spawn(move |_| {
                        vec.lock().unwrap().push(i);
                    });
                }
            });
            vec.into_inner().unwrap()
        })
    }};
}

// FIXME: We should fix or remove this ignored test.
#[test]
#[ignore]
#[cfg_attr(any(target_os = "emscripten", target_family = "wasm"), ignore)]
fn scope_lifo_order() {
    let vec = test_scope_order!(scope => spawn);
    let expected: Vec<i32> = (0..10).rev().collect(); // LIFO -> reversed
    assert_eq!(vec, expected);
}

// FIXME: We should fix or remove this ignored test.
#[test]
#[ignore]
#[cfg_attr(any(target_os = "emscripten", target_family = "wasm"), ignore)]
fn scope_fifo_order() {
    let vec = test_scope_order!(scope_fifo => spawn_fifo);
    let expected: Vec<i32> = (0..10).collect(); // FIFO -> natural order
    assert_eq!(vec, expected);
}

macro_rules! test_spawn_order {
    ($spawn:ident) => {{
        let builder = ThreadPoolBuilder::new().num_threads(1);
        let pool = &builder.build().unwrap();
        let (tx, rx) = channel();
        pool.install(move || {
            for i in 0..10 {
                let tx = tx.clone();
                pool.$spawn(move || {
                    tx.send(i).unwrap();
                });
            }
        });
        rx.iter().collect::<Vec<i32>>()
    }};
}

#[test]
#[cfg_attr(any(target_os = "emscripten", target_family = "wasm"), ignore)]
fn spawn_lifo_order() {
    let vec = test_spawn_order!(spawn);
    let expected: Vec<i32> = (0..10).rev().collect(); // LIFO -> reversed
    assert_eq!(vec, expected);
}

#[test]
#[cfg_attr(any(target_os = "emscripten", target_family = "wasm"), ignore)]
fn spawn_fifo_order() {
    let vec = test_spawn_order!(spawn_fifo);
    let expected: Vec<i32> = (0..10).collect(); // FIFO -> natural order
    assert_eq!(vec, expected);
}

// FIXME: We should fix or remove this ignored test.
#[test]
#[ignore]
#[cfg_attr(any(target_os = "emscripten", target_family = "wasm"), ignore)]
fn nested_scopes() {
    // Create matching scopes for every thread pool.
    fn nest<'scope, OP>(pools: &[ThreadPool], scopes: Vec<&Scope<'scope>>, op: OP)
    where
        OP: FnOnce(&[&Scope<'scope>]) + Send,
    {
        if let Some((pool, tail)) = pools.split_first() {
            pool.scope(move |s| {
                // This move reduces the reference lifetimes by variance to match s,
                // but the actual scopes are still tied to the invariant 'scope.
                let mut scopes = scopes;
                scopes.push(s);
                nest(tail, scopes, op)
            })
        } else {
            (op)(&scopes)
        }
    }

    let pools: Vec<_> =
        (0..10).map(|_| ThreadPoolBuilder::new().num_threads(1).build().unwrap()).collect();

    let counter = AtomicUsize::new(0);
    nest(&pools, vec![], |scopes| {
        for &s in scopes {
            s.spawn(|_| {
                // Our 'scope lets us borrow the counter in every pool.
                counter.fetch_add(1, Ordering::Relaxed);
            });
        }
    });
    assert_eq!(counter.into_inner(), pools.len());
}

// FIXME: We should fix or remove this ignored test.
#[test]
#[ignore]
#[cfg_attr(any(target_os = "emscripten", target_family = "wasm"), ignore)]
fn nested_fifo_scopes() {
    // Create matching fifo scopes for every thread pool.
    fn nest<'scope, OP>(pools: &[ThreadPool], scopes: Vec<&ScopeFifo<'scope>>, op: OP)
    where
        OP: FnOnce(&[&ScopeFifo<'scope>]) + Send,
    {
        if let Some((pool, tail)) = pools.split_first() {
            pool.scope_fifo(move |s| {
                // This move reduces the reference lifetimes by variance to match s,
                // but the actual scopes are still tied to the invariant 'scope.
                let mut scopes = scopes;
                scopes.push(s);
                nest(tail, scopes, op)
            })
        } else {
            (op)(&scopes)
        }
    }

    let pools: Vec<_> =
        (0..10).map(|_| ThreadPoolBuilder::new().num_threads(1).build().unwrap()).collect();

    let counter = AtomicUsize::new(0);
    nest(&pools, vec![], |scopes| {
        for &s in scopes {
            s.spawn_fifo(|_| {
                // Our 'scope lets us borrow the counter in every pool.
                counter.fetch_add(1, Ordering::Relaxed);
            });
        }
    });
    assert_eq!(counter.into_inner(), pools.len());
}

#[test]
#[cfg_attr(any(target_os = "emscripten", target_family = "wasm"), ignore)]
fn in_place_scope_no_deadlock() {
    let pool = ThreadPoolBuilder::new().num_threads(1).build().unwrap();
    let (tx, rx) = channel();
    let rx_ref = &rx;
    pool.in_place_scope(move |s| {
        // With regular scopes this closure would never run because this scope op
        // itself would block the only worker thread.
        s.spawn(move |_| {
            tx.send(()).unwrap();
        });
        rx_ref.recv().unwrap();
    });
}

#[test]
#[cfg_attr(any(target_os = "emscripten", target_family = "wasm"), ignore)]
fn in_place_scope_fifo_no_deadlock() {
    let pool = ThreadPoolBuilder::new().num_threads(1).build().unwrap();
    let (tx, rx) = channel();
    let rx_ref = &rx;
    pool.in_place_scope_fifo(move |s| {
        // With regular scopes this closure would never run because this scope op
        // itself would block the only worker thread.
        s.spawn_fifo(move |_| {
            tx.send(()).unwrap();
        });
        rx_ref.recv().unwrap();
    });
}

#[test]
fn yield_now_to_spawn() {
    let (tx, rx) = channel();

    // Queue a regular spawn.
    crate::spawn(move || tx.send(22).unwrap());

    // The single-threaded fallback mode (for wasm etc.) won't
    // get a chance to run the spawn if we never yield to it.
    crate::registry::in_worker(move |_, _| {
        crate::yield_now();
    });

    // The spawn **must** have started by now, but we still might have to wait
    // for it to finish if a different thread stole it first.
    assert_eq!(22, rx.recv().unwrap());
}

#[test]
fn yield_local_to_spawn() {
    let (tx, rx) = channel();

    // Queue a regular spawn.
    crate::spawn(move || tx.send(22).unwrap());

    // The single-threaded fallback mode (for wasm etc.) won't
    // get a chance to run the spawn if we never yield to it.
    crate::registry::in_worker(move |_, _| {
        crate::yield_local();
    });

    // The spawn **must** have started by now, but we still might have to wait
    // for it to finish if a different thread stole it first.
    assert_eq!(22, rx.recv().unwrap());
}

// Trust (RUSTC-FRONTEND-TOKEN-LEAK-1): the thread-slot handlers as the
// compiler's jobserver proxy sees them: who holds a slot, and who asked.
mod trust_thread_slots {
    use std::collections::HashMap;
    use std::sync::{Arc, Mutex};
    use std::thread::{self, ThreadId};
    use std::time::{Duration, Instant};

    use crate::ThreadPoolBuilder;

    #[derive(Default)]
    struct Slots {
        /// Per thread: slots acquired, slots released.
        threads: HashMap<ThreadId, (usize, usize)>,
        /// Per acquire: who acquired, and how many more slots the other
        /// threads had acquired than released. The test thread counts as -1
        /// there while it waits, because it never acquired its first slot.
        acquires: Vec<(ThreadId, isize)>,
    }

    impl Slots {
        fn total_acquires(&self) -> usize {
            self.acquires.len()
        }

        /// Every thread that used a slot has given it back. The test thread
        /// starts out holding one it never acquired, as the compiler's main
        /// thread does, so its releases and acquires also come in pairs.
        fn balanced(&self) -> bool {
            self.threads.values().all(|(acquired, released)| acquired == released)
        }
    }

    fn pool_with_slots(threads: usize) -> (crate::ThreadPool, Arc<Mutex<Slots>>) {
        let (builder, slots) = builder_with_slots(threads);
        (builder.build().unwrap(), slots)
    }

    fn builder_with_slots(threads: usize) -> (ThreadPoolBuilder, Arc<Mutex<Slots>>) {
        let slots = Arc::new(Mutex::new(Slots::default()));
        let (on_acquire, on_release) = (Arc::clone(&slots), Arc::clone(&slots));
        let builder = ThreadPoolBuilder::new()
            .num_threads(threads)
            .acquire_thread_handler(move || {
                let me = thread::current().id();
                let mut slots = on_acquire.lock().unwrap();
                let others = slots
                    .threads
                    .iter()
                    .filter(|(id, _)| **id != me)
                    .map(|(_, (acquired, released))| *acquired as isize - *released as isize)
                    .sum();
                slots.threads.entry(me).or_default().0 += 1;
                slots.acquires.push((me, others));
            })
            .release_thread_handler(move || {
                let me = thread::current().id();
                on_release.lock().unwrap().threads.entry(me).or_default().1 += 1;
            });
        (builder, slots)
    }

    /// A sleeping worker woken only to terminate takes no thread slot, and
    /// the acquires and releases of every thread still pair up.
    #[test]
    #[cfg_attr(any(target_os = "emscripten", target_family = "wasm"), ignore)]
    fn a_worker_woken_to_terminate_acquires_no_thread_slot() {
        const THREADS: usize = 4;
        let (pool, slots) = pool_with_slots(THREADS);
        pool.install(|| ());
        // Wait until every worker has started and gone to sleep, having
        // released its slot. Balanced slots alone do not say that: a worker
        // woken for the job above (or by the worker that found it) has no slot
        // either until it runs again, and would then take one legitimately.
        // A woken worker is no longer counted as asleep, so once all are
        // counted nothing wakes one again before termination, and from then
        // on balanced slots mean every one of them released.
        let deadline = Instant::now() + Duration::from_secs(60);
        let before = loop {
            if pool.registry.sleeping_threads() == THREADS {
                let slots = slots.lock().unwrap();
                if slots.threads.len() == THREADS + 1 && slots.balanced() {
                    break slots.total_acquires();
                }
            }
            assert!(Instant::now() < deadline, "workers did not go to sleep");
            thread::sleep(Duration::from_millis(1));
        };
        let me = thread::current().id();
        pool.wait_until_stopped();
        let slots = slots.lock().unwrap();
        assert!(slots.balanced(), "an acquire or a release lost its pair");
        assert_eq!(
            slots.total_acquires(),
            before + 1,
            "a terminating worker acquired a thread slot"
        );
        assert_eq!(slots.acquires.last(), Some(&(me, 0)));
    }

    /// A worker whose thread starts after the pool was told to terminate runs
    /// no job, and so neither waits for a thread slot nor takes one.
    #[test]
    #[cfg_attr(any(target_os = "emscripten", target_family = "wasm"), ignore)]
    fn a_worker_started_after_termination_acquires_no_thread_slot() {
        let (builder, slots) = builder_with_slots(3);
        let mut late = Vec::new();
        let pool = builder
            .spawn_handler(|thread| {
                late.push(thread);
                Ok(())
            })
            .build()
            .unwrap();
        drop(pool);
        let workers: Vec<_> =
            late.into_iter().map(|thread| thread::spawn(move || thread.run())).collect();
        for worker in workers {
            worker.join().unwrap();
        }
        let slots = slots.lock().unwrap();
        assert_eq!(slots.total_acquires(), 0, "a worker with nothing to run took a thread slot");
        assert!(slots.balanced());
    }

    /// The thread that tears the pool down takes its slot back only when no
    /// worker holds one, whether the workers were asleep or still running.
    #[test]
    #[cfg_attr(any(target_os = "emscripten", target_family = "wasm"), ignore)]
    fn pool_teardown_takes_its_slot_back_after_every_worker_released() {
        let me = thread::current().id();
        for _ in 0..200 {
            let (pool, slots) = pool_with_slots(3);
            pool.install(|| ());
            // No pause: the worker that ran the job is usually still awake.
            pool.wait_until_stopped();
            let slots = slots.lock().unwrap();
            assert!(slots.balanced(), "an acquire or a release lost its pair");
            assert_eq!(
                slots.acquires.last(),
                Some(&(me, 0)),
                "teardown asked for a slot while a worker still held one"
            );
        }
    }
}
