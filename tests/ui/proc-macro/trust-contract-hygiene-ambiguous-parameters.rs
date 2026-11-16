//@ check-fail
//@ compile-flags: -Z trust-verify=off
//@ dont-check-compiler-stderr

// A call-site metavariable and a definition-site identifier may have the same
// displayed spelling while remaining distinct Rust parameters. Native
// proposition payloads erase that SyntaxContext, so the complete contract
// bundle must be rejected before a function clause or loop clause can select
// either HIR identity by traversal order.
macro_rules! emit_ambiguous_contract {
    ($call_site_x:ident) => {
        fn ambiguous_contract(
            mut n: u32,
            //~^ ERROR parameter `n` and a contract clause of this function have different macro hygiene
            $call_site_x: u32,
            //~^ ERROR parameter `x` and a contract clause of this function have different macro hygiene
            x: u32, //~ ERROR parameters named `x` have distinct hygienic identities
            //~^ ERROR parameter `x` and a contract clause of this function have different macro hygiene
        ) requires x == x {
            while n > 0 invariant x == x decreases n {
                n -= 1;
            }
            let _ = ($call_site_x, x);
        }
    };
}

emit_ambiguous_contract!(x);

fn main() {}
