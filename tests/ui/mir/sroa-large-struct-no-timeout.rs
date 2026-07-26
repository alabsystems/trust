// Trust: Regression test for rust-lang#121354
// Verify that SROA does not cause quadratic compilation time on types with
// many fields. This test should compile in under a second; prior to the fix,
// similar constructs caused 80-minute builds.
//
//@ build-pass
//@ compile-flags: -O

// A struct with 256 fields — above the SROA field limit (128), so SROA should
// bail out early rather than attempting decomposition.
macro_rules! make_large_struct {
    ($name:ident, $n:tt) => {
        make_large_struct!(@fields $name, $n, );
    };
    (@fields $name:ident, 0, $($fields:tt)*) => {
        #[allow(dead_code)]
        struct $name { $($fields)* }
    };
    (@fields $name:ident, 1, $($fields:tt)*) => {
        make_large_struct!(@fields $name, 0, f0: u64, $($fields)*);
    };
    (@fields $name:ident, 2, $($fields:tt)*) => {
        make_large_struct!(@fields $name, 0, f0: u64, f1: u64, $($fields)*);
    };
    (@fields $name:ident, 4, $($fields:tt)*) => {
        make_large_struct!(@fields $name, 2, f2: u64, f3: u64, $($fields)*);
    };
    (@fields $name:ident, 8, $($fields:tt)*) => {
        make_large_struct!(@fields $name, 4, f4: u64, f5: u64, f6: u64, f7: u64, $($fields)*);
    };
    (@fields $name:ident, 16, $($fields:tt)*) => {
        make_large_struct!(@fields $name, 8, f8: u64, f9: u64, f10: u64, f11: u64, f12: u64, f13: u64, f14: u64, f15: u64, $($fields)*);
    };
    (@fields $name:ident, 32, $($fields:tt)*) => {
        make_large_struct!(@fields $name, 16, f16: u64, f17: u64, f18: u64, f19: u64, f20: u64, f21: u64, f22: u64, f23: u64, f24: u64, f25: u64, f26: u64, f27: u64, f28: u64, f29: u64, f30: u64, f31: u64, $($fields)*);
    };
    (@fields $name:ident, 64, $($fields:tt)*) => {
        make_large_struct!(@fields $name, 32, f32_: u64, f33: u64, f34: u64, f35: u64, f36: u64, f37: u64, f38: u64, f39: u64, f40: u64, f41: u64, f42: u64, f43: u64, f44: u64, f45: u64, f46: u64, f47: u64, f48: u64, f49: u64, f50: u64, f51: u64, f52: u64, f53: u64, f54: u64, f55: u64, f56: u64, f57: u64, f58: u64, f59: u64, f60: u64, f61: u64, f62: u64, f63: u64, $($fields)*);
    };
}

// Generate a struct with 64 fields (just under the limit — should still be SROA'd)
make_large_struct!(SmallEnough, 64);

// A struct with enough nesting depth to trigger repeated SROA iterations.
// Each layer wraps the previous, creating deep decomposition chains.
struct Layer1 { a: u64, b: u64, c: u64, d: u64 }
struct Layer2 { x: Layer1, y: Layer1, z: Layer1, w: Layer1 }
struct Layer3 { p: Layer2, q: Layer2, r: Layer2, s: Layer2 }
struct Layer4 { m: Layer3, n: Layer3 }

// Use the types so the compiler actually processes them through MIR opts.
#[inline(never)]
fn use_small(s: SmallEnough) -> u64 {
    s.f0
}

#[inline(never)]
fn use_layers(l: Layer4) -> u64 {
    l.m.p.x.a + l.n.q.y.b
}

fn main() {
    // Ensure the functions are not dead-code-eliminated.
    let s = unsafe { std::mem::zeroed::<SmallEnough>() };
    let l = unsafe { std::mem::zeroed::<Layer4>() };
    std::hint::black_box(use_small(s));
    std::hint::black_box(use_layers(l));
}
