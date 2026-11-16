use super::*;
use crate::getopts;

fn parse(args: &[&str]) -> Matches {
    let mut options = getopts::Options::new();
    for name in [
        "resource-worker-v2",
        "resource-worker-v3",
        "resource-subgroups-v3",
        "resource-bootstrap-fixed-v1",
    ] {
        options.optflag("", name, "");
    }
    options.optopt("", "explain", "", "CODE");
    options.optflag("V", "version", "");
    options.parse(args).unwrap()
}

#[test]
fn malformed_custody_markers_refuse_before_any_mode() {
    for args in [
        vec!["--resource-worker-v3"],
        vec!["--resource-subgroups-v3"],
        vec!["--resource-worker-v3", "--resource-subgroups-v3", "--resource-worker-v2"],
    ] {
        let matches = parse(&args);
        assert!(refusal(&matches, Phase::Options).is_some());
        assert!(refusal(&matches, Phase::Backend).is_some());
    }
}

#[test]
fn producing_context_cannot_enter_early_backend_or_pager() {
    let producing = ["--resource-worker-v3", "--resource-subgroups-v3"];
    let matches = parse(&producing);
    assert!(refusal(&matches, Phase::Options).is_none());
    assert!(refusal(&matches, Phase::Backend).is_some());
    for args in [
        vec![producing[0], producing[1], "--version"],
        vec![producing[0], producing[1], "--explain=E0001"],
        vec![producing[0], producing[1], "--explain", "E0001"],
    ] {
        let matches = parse(&args);
        assert!(refusal(&matches, Phase::Backend).is_some());
    }
    assert!(refusal(&parse(&["--version"]), Phase::Backend).is_none());
    assert!(refusal(&parse(&["--explain=E0001"]), Phase::Options).is_none());
    assert!(
        refusal(&parse(&[producing[0], producing[1], "--explain=E0001"]), Phase::Options).is_some()
    );
}

#[test]
fn private_fixed_backend_and_pager_never_enter_ordinary_raw_execution() {
    let private = "--resource-bootstrap-fixed-v1";
    assert!(refusal(&parse(&[private]), Phase::Options).is_none());
    assert!(refusal(&parse(&[private]), Phase::Backend).is_some());
    assert!(refusal(&parse(&[private, "--explain=E0001"]), Phase::Options).is_some());
    for other in ["--resource-worker-v2", "--resource-worker-v3", "--resource-subgroups-v3"] {
        assert!(refusal(&parse(&[private, other]), Phase::Options).is_some());
    }
}
