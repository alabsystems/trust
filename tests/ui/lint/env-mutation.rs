// Checks the trust-only `env_mutation` lint (warn-by-default; `#![deny]` here to
// exercise the hard-error path): every call to `std::env::set_var` /
// `std::env::remove_var` (or use of them as values) in a local crate is reported;
// `#[allow(env_mutation)]` scopes a blessed site.

//@ edition: 2024

#![deny(env_mutation)]

fn main() {
    unsafe {
        std::env::set_var("ENV_MUTATION_UI", "1");
        //~^ ERROR call to `std::env::set_var` mutates the process-global environment
        std::env::remove_var("ENV_MUTATION_UI");
        //~^ ERROR call to `std::env::remove_var` mutates the process-global environment
    }

    let indirect = std::env::set_var::<&str, &str>;
    //~^ ERROR use of `std::env::set_var` as a function value
    let _ = indirect;

    blessed();
}

// An explicit `#[allow]` is scoping an exception, not disabling the check.
#[allow(env_mutation)]
fn blessed() {
    unsafe { std::env::set_var("ENV_MUTATION_UI", "blessed") };
}
