//! Share a successfully constructed immutable value within this process.
//!
//! Ordinary failures are not remembered: a later caller can retry after a
//! resource stop. A panicking initializer poisons admission, so it cannot turn
//! an incomplete construction into a value. Callers choose the stack on which
//! initialization runs; waiting callers never start duplicate constructions.

use std::sync::{Mutex, OnceLock};

pub(crate) struct CheckedOnce<T> {
    value: OnceLock<T>,
    initializer: Mutex<()>,
}

impl<T> CheckedOnce<T> {
    pub(crate) const fn new() -> Self {
        Self { value: OnceLock::new(), initializer: Mutex::new(()) }
    }

    pub(crate) fn get_or_try_init(&self, build: impl FnOnce() -> Option<T>) -> Option<&T> {
        if let Some(value) = self.value.get() {
            return Some(value);
        }
        let _guard = self.initializer.lock().ok()?;
        if self.value.get().is_none() {
            self.value.set(build()?).ok()?;
        }
        self.value.get()
    }
}

#[cfg(test)]
mod tests {
    use std::sync::atomic::{AtomicUsize, Ordering};
    use std::sync::{Arc, Barrier};

    use super::CheckedOnce;

    #[test]
    fn a_failed_construction_can_retry_without_publishing_a_value() {
        let value = CheckedOnce::new();
        let calls = AtomicUsize::new(0);
        assert_eq!(
            value.get_or_try_init(|| {
                calls.fetch_add(1, Ordering::SeqCst);
                None
            }),
            None
        );
        assert_eq!(
            value.get_or_try_init(|| {
                calls.fetch_add(1, Ordering::SeqCst);
                Some(41)
            }),
            Some(&41)
        );
        assert_eq!(value.get_or_try_init(|| panic!("already initialized")), Some(&41));
        assert_eq!(calls.load(Ordering::SeqCst), 2);
    }

    #[test]
    fn concurrent_callers_share_one_successful_construction() {
        let value = Arc::new(CheckedOnce::new());
        let calls = Arc::new(AtomicUsize::new(0));
        let barrier = Arc::new(Barrier::new(8));
        let threads: Vec<_> = (0..8)
            .map(|_| {
                let (value, calls, barrier) = (value.clone(), calls.clone(), barrier.clone());
                std::thread::spawn(move || {
                    barrier.wait();
                    let result = value
                        .get_or_try_init(|| {
                            calls.fetch_add(1, Ordering::SeqCst);
                            Some(73)
                        })
                        .expect("successful construction");
                    (*result, std::ptr::from_ref(result) as usize)
                })
            })
            .collect();
        let results: Vec<_> = threads.into_iter().map(|t| t.join().unwrap()).collect();
        assert!(results.iter().all(|result| *result == results[0]));
        assert_eq!(results[0].0, 73);
        assert_eq!(calls.load(Ordering::SeqCst), 1);
    }

    #[test]
    fn a_panicking_initializer_cannot_publish_or_admit_a_replacement() {
        let value = CheckedOnce::<u32>::new();
        assert!(
            std::panic::catch_unwind(|| {
                value.get_or_try_init(|| panic!("incomplete construction"))
            })
            .is_err()
        );
        assert!(value.get_or_try_init(|| Some(99)).is_none());
    }
}
