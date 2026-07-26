// Test that borrowck handles functions with many local variables without
// quadratic compile-time blowup in EverInitializedPlaces analysis.
// Regression test for rust-lang#144635.
//
// Trust: When init count exceeds 4096, EverInitializedPlaces falls back to
// conservative "all initialized" approximation to avoid O(inits * blocks)
// quadratic behavior.

//@ check-pass
//@ compile-flags: -C opt-level=0

// Generate a function with many locals to stress the EverInitializedPlaces
// analysis. Each match arm creates multiple MIR locals and init indices.
fn many_locals() -> u64 {
    let mut sum = 0u64;
    // Use a series of independent let bindings and drops to create many
    // move paths and init points in MIR.
    macro_rules! make_locals {
        ($($n:ident),*) => {
            $(
                let $n = Box::new(1u64);
                sum += *$n;
                drop($n);
            )*
        };
    }

    // 200 locals is enough to generate many init indices (each Box creates
    // multiple MIR locals for the allocation), while keeping the test file
    // reasonably sized. The actual cap is 4096 init indices.
    make_locals!(
        a001, a002, a003, a004, a005, a006, a007, a008, a009, a010,
        a011, a012, a013, a014, a015, a016, a017, a018, a019, a020,
        a021, a022, a023, a024, a025, a026, a027, a028, a029, a030,
        a031, a032, a033, a034, a035, a036, a037, a038, a039, a040,
        a041, a042, a043, a044, a045, a046, a047, a048, a049, a050,
        a051, a052, a053, a054, a055, a056, a057, a058, a059, a060,
        a061, a062, a063, a064, a065, a066, a067, a068, a069, a070,
        a071, a072, a073, a074, a075, a076, a077, a078, a079, a080,
        a081, a082, a083, a084, a085, a086, a087, a088, a089, a090,
        a091, a092, a093, a094, a095, a096, a097, a098, a099, a100,
        a101, a102, a103, a104, a105, a106, a107, a108, a109, a110,
        a111, a112, a113, a114, a115, a116, a117, a118, a119, a120,
        a121, a122, a123, a124, a125, a126, a127, a128, a129, a130,
        a131, a132, a133, a134, a135, a136, a137, a138, a139, a140,
        a141, a142, a143, a144, a145, a146, a147, a148, a149, a150,
        a151, a152, a153, a154, a155, a156, a157, a158, a159, a160,
        a161, a162, a163, a164, a165, a166, a167, a168, a169, a170,
        a171, a172, a173, a174, a175, a176, a177, a178, a179, a180,
        a181, a182, a183, a184, a185, a186, a187, a188, a189, a190,
        a191, a192, a193, a194, a195, a196, a197, a198, a199, a200
    );

    sum
}

fn main() {
    let _ = many_locals();
}
