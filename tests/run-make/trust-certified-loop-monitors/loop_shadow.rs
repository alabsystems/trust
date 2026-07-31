fn shadowed_loop(n: u32) -> u32 {
    let n = n + 100;
    let inner_result = {
        let mut n = 3u32;
        while n > 0 invariant n <= 3 decreases n {
            n -= 1;
        }
        n
    };
    // Keep the same-typed outer shadow live so a name-based monitor binding
    // would observe the wrong value and fail the invariant.
    inner_result + (n - 100)
}

#[test]
fn debuginfo_free_monitor_uses_exact_shadow_identity() {
    assert_eq!(shadowed_loop(0), 0);
}
