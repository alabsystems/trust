use super::*;

// Count only this thread's test interval. Other parallel tests and fixture
// construction are excluded; malformed text must not allocate per separator.
struct CountingAllocator;
thread_local! {static ALLOCATED:std::cell::Cell<Option<usize>>=const{std::cell::Cell::new(None)};}
#[global_allocator]
static ALLOCATOR: CountingAllocator = CountingAllocator;
unsafe impl std::alloc::GlobalAlloc for CountingAllocator {
    unsafe fn alloc(&self, layout: std::alloc::Layout) -> *mut u8 {
        ALLOCATED.with(|count| {
            if let Some(bytes) = count.get() {
                count.set(Some(bytes.saturating_add(layout.size())))
            }
        });
        unsafe { std::alloc::System.alloc(layout) }
    }
    unsafe fn dealloc(&self, pointer: *mut u8, layout: std::alloc::Layout) {
        unsafe { std::alloc::System.dealloc(pointer, layout) }
    }
    unsafe fn realloc(&self, pointer: *mut u8, layout: std::alloc::Layout, size: usize) -> *mut u8 {
        ALLOCATED.with(|count| {
            if let Some(bytes) = count.get() {
                count.set(Some(bytes.saturating_add(size)))
            }
        });
        unsafe { std::alloc::System.realloc(pointer, layout, size) }
    }
}

#[test]
fn malformed_elapsed_separator_population_does_not_allocate_a_separator_vector() {
    let original = inventory();
    let text = summary(2, 0, 0, 0, 0).replace("0.02s", &format!("{}s", ".".repeat(1024 * 1024)));
    ALLOCATED.with(|count| count.set(Some(0)));
    let result = original.validate_sample(text.as_bytes(), b"");
    let allocated = ALLOCATED.with(|count| count.replace(None)).unwrap();
    assert!(result.is_err());
    assert!(allocated < 64 * 1024, "malformed one-MiB elapsed field allocated {allocated} bytes");
}

fn inventory() -> Inventory {
    Inventory::parse(b"beta: test\nalpha: test\n\n2 tests, 0 benchmarks\n").unwrap()
}

fn summary(passed: u64, failed: u64, ignored: u64, measured: u64, filtered: u64) -> String {
    format!(
        "running 2 tests\ntest alpha ... ok\ntest beta ... ok\n\ntest result: ok. {passed} passed; {failed} failed; {ignored} ignored; {measured} measured; {filtered} filtered out; finished in 0.02s\n\n"
    )
}

#[test]
fn discovery_retains_all_sorted_names_and_exact_native_plural_counts() {
    assert_eq!(inventory().cases(), &["alpha", "beta"]);
    assert_eq!(Inventory::parse(b"one: test\n\n1 test, 0 benchmarks\n").unwrap().cases(), &["one"]);
    for bytes in [
        b"0 tests, 0 benchmarks\n".as_slice(),
        b"one: test\none: test\n2 tests, 0 benchmarks\n",
        b"one: test\n2 tests, 0 benchmarks\n",
        b"one: test\n1 tests, 0 benchmarks\n",
        b"one: test\n",
        b"one: test\n1 test, 0 benchmarks\none_more: test\n",
        b"bench: benchmark\n1 benchmark\n",
        b"one: test\n1 test, 1 benchmark\n",
    ] {
        assert!(Inventory::parse(bytes).is_err(), "{bytes:?}");
    }
}

#[test]
fn sample_requires_the_complete_original_denominator_without_skips_or_filters() {
    let original = inventory();
    assert_eq!(
        original
            .validate_sample(summary(2, 0, 0, 0, 0).as_bytes(), b"diagnostic\n")
            .unwrap()
            .passed,
        2
    );
    assert_eq!(original.validate_sample(summary(2, 0, 0, 0, 0).as_bytes(), b"").unwrap().passed, 2);
    for counts in
        [(1, 0, 0, 0, 0), (2, 1, 0, 0, 0), (2, 0, 1, 0, 0), (2, 0, 0, 1, 0), (2, 0, 0, 0, 1)]
    {
        assert!(
            original
                .validate_sample(
                    summary(counts.0, counts.1, counts.2, counts.3, counts.4).as_bytes(),
                    b"\n"
                )
                .is_err()
        );
    }
}

#[test]
fn duplicate_failed_replaced_and_malformed_summary_bytes_never_satisfy_a_sample() {
    let original = inventory();
    let pass = summary(2, 0, 0, 0, 0);
    for stdout in [
        format!("{pass}{pass}"),
        format!("test result: FAILED. earlier\n{pass}"),
        format!("SKIPPED: unsupported native body\n{pass}"),
        pass.replace("2 passed", "2.0 passed"),
        pass.replace("2 passed", "02 passed"),
        pass.replace("2 passed", "18446744073709551616 passed"),
        pass.replace("0.02s", "NaNs"),
        pass.replace("0.02s", "1e3s"),
        pass.replace("filtered out;", "filtered out; unexpected;"),
    ] {
        assert!(original.validate_sample(stdout.as_bytes(), b"\n").is_err(), "{stdout:?}");
    }
    assert!(original.validate_sample(b"\n", pass.as_bytes()).is_err());
    assert!(original.validate_sample(pass.as_bytes(), b"test result: FAILED. child\n").is_err());
}

#[test]
fn incomplete_non_utf8_and_nul_captures_refuse_without_normalization() {
    for bytes in [b"one: test".as_slice(), b"\xff\n", b"one\0: test\n"] {
        assert!(Inventory::parse(bytes).is_err());
    }
    let original = inventory();
    let pass = summary(2, 0, 0, 0, 0);
    assert!(original.validate_sample(pass.trim_end().as_bytes(), b"\n").is_err());
}
