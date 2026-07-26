// Regression: a `#[requires(x < 100)] #[ensures(ret > x)] fn inc(x) { x + 1 }`
// contract must produce WELL-FORMED VCs:
//   (1) NO "unparseable contract" fail-closed Assertion — the compiler-lowered
//       `__trust_lowered_compiler_contract__:` prefix must be stripped & parsed.
//   (2) the Postcondition VC must PIN the return value to its definition
//       (`_0 == _4.0`) so it is dischargeable (not havoc'd to a spurious cex).
// Without these the contract was false-refuted with a `_0 = 0` / `x = 0` cex
// even though it holds. The fixture is the REAL extracted MIR (-Ztrust-dump=mir:<dir>).
use trust_types::*;
use trust_vcgen::generate_vcs;

#[test]
fn contract_vcs_are_well_formed() {
    let func: VerifiableFunction =
        serde_json::from_str(include_str!("fixtures/contract_inc_mir.json"))
            .expect("fixture MIR must deserialize");
    let vcs = generate_vcs(&func);

    for vc in &vcs {
        if let VcKind::Assertion { message } = &vc.kind {
            assert!(
                !message.contains("unparseable"),
                "compiler-lowered contract must parse, not fail closed: {message}"
            );
        }
    }

    let post = vcs
        .iter()
        .find(|vc| matches!(vc.kind, VcKind::Postcondition))
        .expect("the #[ensures] clause should produce a Postcondition VC");
    let dbg = format!("{:?}", post.formula);
    assert!(
        dbg.contains("Eq(Var(\"_0\""),
        "postcondition must pin the return value `_0` to its definition: {dbg}"
    );
}
