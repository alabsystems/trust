// The Clean-origin purity guard resolves a trait-method callee to the IMPL that
// runs, not to the trait item's DEFAULT body. Both callees here are PURE at the
// impl and must compile: the guard used to refuse them because it walked the
// wrong body (an impure default) or found no body at all (no default body, so
// the trait item has no MIR). The impure-impl-behind-a-pure-default twin is
// refused, and is pinned check-fail in
// tests/ui/trust/clean_origin_trait_impl_callee_purity.rs.
use std::sync::atomic::{AtomicU64, Ordering};

static COUNTER: AtomicU64 = AtomicU64::new(0);

// An IMPURE default body, overridden by a PURE impl: the impl is what runs.
trait Bump {
    fn bump(_x: u64) -> u64 {
        COUNTER.fetch_add(1, Ordering::SeqCst) + 1
    }
}
struct PureBump;
impl Bump for PureBump {
    fn bump(x: u64) -> u64 {
        x.wrapping_add(1)
    }
}
fn bump(x: u64) -> u64 {
    <PureBump as Bump>::bump(x)
}

// NO default body at all: the trait item has no MIR, the impl does.
trait Double {
    fn double(x: u64) -> u64;
}
struct PureDouble;
impl Double for PureDouble {
    fn double(x: u64) -> u64 {
        x.wrapping_mul(2)
    }
}
fn double(x: u64) -> u64 {
    <PureDouble as Double>::double(x)
}

clean {
    def twice_bump (x : UInt64) : UInt64 := bump (bump x)
    def double_it (x : UInt64) : UInt64 := double x
}

fn main() {
    assert_eq!(twice_bump(5), 7);
    assert_eq!(double_it(21), 42);
    println!("twice_bump(5) = {}", twice_bump(5));
}
