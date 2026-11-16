use super::{direct_link_args, thread_limit};
#[test]
fn automatic_direct_link_preserves_native_driver_forwarding_and_order() {
    let args = [
        "-Wl,-fixup_chains".into(),
        "-Wl,-rpath,/tmp/path with spaces".into(),
        "-Xlinker".into(),
        "-dead_strip".into(),
        "object.o".into(),
        "-Wl,,tail".into(),
    ];
    assert_eq!(
        direct_link_args(&args).unwrap(),
        ["-fixup_chains", "-rpath", "/tmp/path with spaces", "-dead_strip", "object.o", "tail"]
    );
    assert!(direct_link_args(&["-Xlinker".into()]).is_err());
    assert_eq!(
        thread_limit(&direct_link_args(&["-Xlinker".into(), "--threads=2".into()]).unwrap(), 28),
        Ok(2)
    );
}

#[test]
fn respects_explicit_caps_and_live_smaller_budget() {
    let args = ["--threads=4".into(), "--thinlto-jobs".into(), "2".into()];
    assert_eq!(thread_limit(&args, 28), Ok(2));
    assert_eq!(thread_limit(&args, 1), Ok(1));
    assert_eq!(thread_limit(&["-Wl,--threads=3".into(), "@rpath/libunit.dylib".into()], 8), Ok(3));
}
#[test]
fn refuses_unbounded_or_opaque_thread_configuration() {
    for value in ["--threads=0", "--threads=all", "@private.rsp", "--read-workers=2"] {
        assert!(thread_limit(&[value.into()], 8).is_err());
    }
}
