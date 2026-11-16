#[path = "reified_charge.rs"] mod subject;
fn main() {
    let pointer_panics = std::panic::catch_unwind(|| subject::reified_counted(255, 1)).is_err();
    let direct_panics = std::panic::catch_unwind(|| subject::direct_counted(255, 1)).is_err();
    let guarded = subject::guarded_counted(255, 1);
    let total = subject::total_counted(255, 1);
    println!("pointer_panics={pointer_panics} direct_panics={direct_panics} guarded={guarded} total={total}");
    assert!(pointer_panics && direct_panics);
    assert_eq!(guarded, 128);
    assert_eq!(total, 255);
    assert_eq!(subject::constructor_pointer(255), 255);
    assert_eq!(subject::total_defined_after(255), 255);
    assert_eq!(subject::total_defined_after_counted(255, 1), 255);
    assert!(std::panic::catch_unwind(|| subject::reassigned_counted(true, 255, 1)).is_err());
    assert!(std::panic::catch_unwind(|| subject::borrowed_counted(255, 1)).is_err());
    assert!(std::panic::catch_unwind(|| subject::parameter_maybe_overwritten(subject::panic_add, false, 255, 1)).is_err());
    assert_eq!(subject::parameter_maybe_overwritten(subject::panic_add, true, 255, 1), 255);
}
