use super::*;

#[test]
#[ignore = "requires an explicitly selected actual native compiler and complete target sysroot"]
fn actual_engineering_target_retains_shared_descriptor_admission() {
    let program = std::env::var_os("TARGO_TEST_ENGINEERING_COMPILER")
        .map(PathBuf::from)
        .expect("explicit actual native compiler input");
    let program = program.canonicalize().unwrap();
    let root = program.parent().unwrap().parent().unwrap();
    let end = Instant::now() + Duration::from_secs(60);
    let compiler =
        Arc::new(HeldProgram::open(root, &program, &digest(&program, end).unwrap(), end).unwrap());
    let target = capture_target(compiler, end).unwrap();
    let files = target.file_observations().count();
    assert!(files > 0);
    target.validate(end).unwrap();
    println!(
        "actual engineering target: files={files} admission={:?}",
        target.admission_observation()
    );
}
