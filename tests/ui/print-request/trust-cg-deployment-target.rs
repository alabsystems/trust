//! A print-only trust-cg session must not interpret rustc's placeholder
//! executable output or default panic=unwind strategy as a codegen request.

//@ needs-trust-cg-backend
//@ only-apple
//@ compile-flags: --print=deployment-target -Zunstable-options -Zcodegen-backend=trust-cg -Ztrust-verify=off
//@ normalize-stdout: "\w*_DEPLOYMENT_TARGET" -> "$$OS_DEPLOYMENT_TARGET"
//@ normalize-stdout: "\d+\." -> "$$CURRENT_MAJOR_VERSION."
//@ normalize-stdout: "\d+" -> "$$CURRENT_MINOR_VERSION"
//@ check-pass

fn main() {}
