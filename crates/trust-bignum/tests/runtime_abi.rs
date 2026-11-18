//! Link and exercise the real nineteen-symbol runtime, including ownership.
//! These controls do not prove handle liveness, source refinement or NoUB.

#[path = "support/handles.rs"]
mod handles;
use handles::*;
use trust_bignum::Nat;

fn producers() -> [(&'static str, Binary); 11] {
    [
        ("add", trust_bignum_nat_add),
        ("sub", trust_bignum_nat_sub),
        ("mul", trust_bignum_nat_mul),
        ("div", trust_bignum_nat_div),
        ("mod", trust_bignum_nat_mod),
        ("land", trust_bignum_nat_land),
        ("lor", trust_bignum_nat_lor),
        ("xor", trust_bignum_nat_xor),
        ("shift_left", trust_bignum_nat_shift_left),
        ("shift_right", trust_bignum_nat_shift_right),
        ("pow", trust_bignum_nat_pow),
    ]
}

#[test]
fn every_producing_symbol_allocates_and_borrows_even_for_identity_or_zero_results() {
    let a = Handle::new(9);
    let b = Handle::new(2);
    let mut results = Vec::new();
    for (name, operation) in producers() {
        let result = a.apply(operation, &b);
        assert_ne!(result.pointer(), a.pointer(), "{name} aliases its first operand");
        assert_ne!(result.pointer(), b.pointer(), "{name} aliases its second operand");
        assert!(results.iter().all(|old: &Handle| old.pointer() != result.pointer()));
        results.push(result);
    }
    let copy = a.duplicate();
    assert_ne!(copy.pointer(), a.pointer());
    assert_eq!(copy.value(), a.value());
    let zero = Handle::new(0);
    let zero_copy = zero.duplicate();
    assert_ne!(zero_copy.pointer(), zero.pointer());
    assert_eq!(zero_copy.value(), &Nat::ZERO);
    // Release every result through the actual drop ABI, then read both inputs.
    drop(results);
    drop(copy);
    assert_eq!(a.value(), &Nat::from_u64(9));
    assert_eq!(b.value(), &Nat::from_u64(2));
}

#[test]
fn binary_shims_allow_one_live_handle_in_both_borrowed_slots() {
    let a = Handle::new(4);
    let expected = [8, 0, 16, 1, 0, 4, 4, 0, 64, 0, 256];
    for ((name, operation), value) in producers().into_iter().zip(expected) {
        let result = a.apply(operation, &a);
        assert_eq!(result.value(), &Nat::from_u64(value), "{name}(4,4)");
        assert_ne!(result.pointer(), a.pointer());
    }
    assert!(unsafe { trust_bignum_nat_beq(a.pointer(), a.pointer()) });
    assert!(unsafe { trust_bignum_nat_ble(a.pointer(), a.pointer()) });
    assert_eq!(a.value(), &Nat::from_u64(4));
}

#[test]
fn comparisons_and_checked_projection_cross_the_limb_boundary() {
    let max = Handle::new(u64::MAX);
    let one = Handle::new(1);
    let wide = max.apply(trust_bignum_nat_add, &one);
    let zero = Handle::new(0);
    assert!(unsafe { trust_bignum_nat_fits_u64(max.pointer()) });
    assert!(!unsafe { trust_bignum_nat_fits_u64(wide.pointer()) });
    assert_eq!(unsafe { trust_bignum_nat_to_u64(max.pointer()) }, u64::MAX);
    assert_eq!(unsafe { trust_bignum_nat_to_u64(zero.pointer()) }, 0);
    assert!(!unsafe { trust_bignum_nat_beq(max.pointer(), wide.pointer()) });
    assert!(unsafe { trust_bignum_nat_ble(max.pointer(), wide.pointer()) });
    assert!(!unsafe { trust_bignum_nat_ble(wide.pointer(), max.pointer()) });
    assert!(unsafe { trust_bignum_nat_is_zero(zero.pointer()) });
    assert!(!unsafe { trust_bignum_nat_is_zero(wide.pointer()) });
}

#[test]
fn zero_division_remainder_and_full_natural_counts_follow_lean() {
    let value = Handle::from_limbs(&[7, 1]);
    let zero = Handle::new(0);
    assert_eq!(value.apply(trust_bignum_nat_div, &zero).value(), &Nat::ZERO);
    assert_eq!(value.apply(trust_bignum_nat_mod, &zero).value(), value.value());
    let huge = Handle::from_limbs(&[0, 1]);
    assert_eq!(value.apply(trust_bignum_nat_shift_right, &huge).value(), &Nat::ZERO);
    assert_eq!(zero.apply(trust_bignum_nat_shift_left, &huge).value(), &Nat::ZERO);
    assert_eq!(zero.apply(trust_bignum_nat_pow, &zero).value(), &Nat::one());
    assert_eq!(zero.apply(trust_bignum_nat_pow, &huge).value(), &Nat::ZERO);
    let one = Handle::new(1);
    assert_eq!(one.apply(trust_bignum_nat_pow, &huge).value(), &Nat::one());
}

#[test]
fn the_runtime_does_not_inherit_kernel_reduction_budgets() {
    let one = Handle::new(1);
    let two = Handle::new(2);
    let shift = Handle::new(2048);
    let mut expected = vec![0; 32];
    expected.push(1);
    assert_eq!(one.apply(trust_bignum_nat_shift_left, &shift).value().limbs(), expected);
    let exponent = Handle::new(1024);
    let mut expected = vec![0; 16];
    expected.push(1);
    assert_eq!(two.apply(trust_bignum_nat_pow, &exponent).value().limbs(), expected);
}

#[cfg(unix)]
mod refusals {
    use std::fs::{self, DirBuilder, OpenOptions};
    use std::io::Read;
    use std::os::unix::fs::{DirBuilderExt, OpenOptionsExt};
    use std::os::unix::process::ExitStatusExt;
    use std::process::{Command, Stdio};
    use std::sync::atomic::{AtomicU64, Ordering};
    use std::time::{Duration, Instant};

    use super::*;

    const CHILD: &str = "TRUST_BIGNUM_ABI_REFUSAL_CHILD";
    static NEXT: AtomicU64 = AtomicU64::new(0);

    /// The helper has no effect in the ordinary parent harness. Every parent
    /// case below runs this SAME image, requires SIGABRT and the exact entry's
    /// diagnostic, and fails if the foreign call returns or the helper panics.
    #[test]
    fn abi_refusal_child() {
        let Ok(case) = std::env::var(CHILD) else { return };
        let value = Handle::new(3);
        if case == "projection-overflow" {
            let max = Handle::new(u64::MAX);
            let wide = max.apply(trust_bignum_nat_add, &Handle::new(1));
            unsafe { trust_bignum_nat_to_u64(wide.pointer()) };
        } else if case == "left-shift-addressability" {
            let count = Handle::from_limbs(&[0, 0, 1]);
            value.apply(trust_bignum_nat_shift_left, &count);
        } else if let Some((name, slot)) = case.rsplit_once(':') {
            let null = core::ptr::null();
            if let Some((_, operation)) = producers().into_iter().find(|(op, _)| *op == name) {
                unsafe {
                    operation(
                        if slot == "a" { null } else { value.pointer() },
                        if slot == "b" { null } else { value.pointer() },
                    );
                }
            } else {
                unsafe {
                    match name {
                        "beq" => {
                            trust_bignum_nat_beq(
                                if slot == "a" { null } else { value.pointer() },
                                if slot == "b" { null } else { value.pointer() },
                            );
                        }
                        "ble" => {
                            trust_bignum_nat_ble(
                                if slot == "a" { null } else { value.pointer() },
                                if slot == "b" { null } else { value.pointer() },
                            );
                        }
                        "is_zero" => {
                            trust_bignum_nat_is_zero(null);
                        }
                        "fits_u64" => {
                            trust_bignum_nat_fits_u64(null);
                        }
                        "to_u64" => {
                            trust_bignum_nat_to_u64(null);
                        }
                        "clone" => {
                            trust_bignum_nat_clone(null);
                        }
                        "drop" => trust_bignum_nat_drop(core::ptr::null_mut()),
                        _ => panic!("unknown child case: {case}"),
                    }
                }
            }
        } else {
            panic!("unknown child case: {case}");
        }
        panic!("C ABI refusal returned: {case}");
    }

    fn must_abort(case: &str, expected: &str) {
        let path = std::env::temp_dir().join(format!(
            "trust-bignum-abi-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed),
        ));
        DirBuilder::new().mode(0o700).create(&path).unwrap();
        let stdout = OpenOptions::new()
            .write(true)
            .create_new(true)
            .mode(0o600)
            .open(path.join("stdout"))
            .unwrap();
        let stderr = OpenOptions::new()
            .write(true)
            .create_new(true)
            .mode(0o600)
            .open(path.join("stderr"))
            .unwrap();
        let mut child = Command::new(std::env::current_exe().unwrap())
            .args(["--exact", "refusals::abi_refusal_child", "--nocapture"])
            .env(CHILD, case)
            .stdin(Stdio::null())
            .stdout(stdout)
            .stderr(stderr)
            .spawn()
            .unwrap();
        let deadline = Instant::now() + Duration::from_secs(10);
        let status = loop {
            if let Some(status) = child.try_wait().unwrap() {
                break status;
            }
            if Instant::now() >= deadline
                || fs::metadata(path.join("stdout")).unwrap().len() > 1024 * 1024
                || fs::metadata(path.join("stderr")).unwrap().len() > 1024 * 1024
            {
                child.kill().unwrap();
                child.wait().unwrap();
                panic!(
                    "bounded ABI refusal child did not finish: {case}; evidence {}",
                    path.display()
                );
            }
            std::thread::sleep(Duration::from_millis(10));
        };
        let mut diagnostic = String::new();
        fs::File::open(path.join("stderr"))
            .unwrap()
            .take(1024 * 1024 + 1)
            .read_to_string(&mut diagnostic)
            .unwrap();
        assert!(diagnostic.len() <= 1024 * 1024);
        assert_eq!(status.signal(), Some(6), "{case}: {status:?}, {diagnostic}");
        assert!(diagnostic.contains(expected), "{case}: {diagnostic}");
        fs::remove_dir_all(path).unwrap();
    }

    #[test]
    fn every_handle_slot_refuses_null_through_the_actual_c_abi() {
        for (name, _) in producers() {
            for slot in ["a", "b"] {
                must_abort(
                    &format!("{name}:{slot}"),
                    &format!("trust_bignum_nat_{name}: a null `Nat` handle"),
                );
            }
        }
        for name in ["beq", "ble"] {
            for slot in ["a", "b"] {
                must_abort(
                    &format!("{name}:{slot}"),
                    &format!("trust_bignum_nat_{name}: a null `Nat` handle"),
                );
            }
        }
        for name in ["is_zero", "fits_u64", "to_u64", "clone", "drop"] {
            must_abort(
                &format!("{name}:a"),
                &format!("trust_bignum_nat_{name}: a null `Nat` handle"),
            );
        }
    }

    #[test]
    fn checked_projection_never_wraps_and_impossible_allocation_never_masks_the_count() {
        must_abort("projection-overflow", "trust_bignum_nat_to_u64: Nat does not fit u64");
        must_abort(
            "left-shift-addressability",
            "Nat::shift_left: result exceeds addressable allocation storage",
        );
    }
}
