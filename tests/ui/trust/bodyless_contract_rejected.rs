//@ compile-flags: -Z trust-verify=off

clean {
    theorem bodyless_bound (n : Nat) : n = n := rfl
}

trait RequiredContract {
    fn required(&self, x: u32) -> u32
        ensures result == x by bodyless_bound;
        //~^ ERROR contract clauses are not supported on required trait method declarations
}

unsafe extern "C" {
    fn foreign(x: u32) -> u32
        ensures result == x by bodyless_bound;
        //~^ ERROR contract clauses are not supported on foreign function declarations
}

fn main() {}
