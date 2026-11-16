//! Compile and exercise the same native frontend boundary without linking a
//! second whole compiler/frontend. This supplies no graph or SDK fixture.
#[path = "../../../targo-trust/src/self_improve/native.rs"]
mod frontend_boundary;

#[test]
fn native_frontend_refuses_before_any_project_or_agent_work() {
    assert_eq!(frontend_boundary::run(true), std::process::ExitCode::from(3));
    assert_eq!(frontend_boundary::run(false), std::process::ExitCode::from(3));
    let mut measurement =
        trust_qualification::improvement::Measurements::new(&["observed".into()]).unwrap();
    measurement.start("observed").unwrap().finish(false);
    let report = frontend_boundary::timing_report(measurement);
    assert_eq!(report["complete"], false);
    assert!(report["measured_bottleneck_candidate"].is_null());
}
