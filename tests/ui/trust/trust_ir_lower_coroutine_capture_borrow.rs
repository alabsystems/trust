//@ dont-check-compiler-stderr
//@ compile-flags: -Ztrust-ir-lower=strict -Ztrust-verify=on -Ztrust-policy=advisory
//@ needs-trust-verify
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
//@ edition: 2021

// Shared references to a coroutine's own captures borrow places, including
// repeated borrows and references selected on different control-flow edges.
// Coroutine-value drop glue remains unsupported in the outer constructor.

async fn repeated(value: u32) -> u32 {
    let a = &value;
    let b = &value;
    *a + *b
}

async fn branches(value: u32, choose: bool) -> u32 {
    let selected = if choose { &value } else { &value };
    *selected + value
}

fn main() {
    //~^ ERROR the effect-conservation check refused it against the built MIR
    let _a = repeated(7);
    let _b = branches(9, true);
}
