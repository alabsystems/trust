// trust-soundness-corpus entry `instance-walk-generic-edge`: the witness. `t()` runs
// the dependency's impl, which writes through null: the process dies with SIGSEGV.
extern crate unverified_edge_instance_dep as dep;
use dep::Act2;

fn g2<T: Act2>(x: &T) -> u32 {
    x.a2()
}

#[inline(never)]
pub fn t() -> u32 {
    g2(&5u32)
}

fn main() {
    println!("calling t()");
    println!("{}", t());
}
