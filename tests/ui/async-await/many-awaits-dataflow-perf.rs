// Regression test for rust-lang#144635: EverInitializedPlaces was very slow
// with many await points because the StorageDead handling iterated per-element
// instead of using bulk bitset operations.
//
// Trust: This test verifies that async functions with many await points
// compile in reasonable time. Before the fix, the EverInitializedPlaces
// dataflow analysis had O(n^2) behavior with n await points.
//
//@ check-pass
//@ edition: 2021

#![allow(unused)]

async fn yield_point() {}

// 100 await points is enough to trigger the quadratic behavior in the
// original implementation while still compiling quickly with the fix.
async fn many_awaits() {
    let a = String::new();
    let b = String::new();
    let c = String::new();

    yield_point().await;
    yield_point().await;
    yield_point().await;
    yield_point().await;
    yield_point().await;
    yield_point().await;
    yield_point().await;
    yield_point().await;
    yield_point().await;
    yield_point().await; // 10

    yield_point().await;
    yield_point().await;
    yield_point().await;
    yield_point().await;
    yield_point().await;
    yield_point().await;
    yield_point().await;
    yield_point().await;
    yield_point().await;
    yield_point().await; // 20

    yield_point().await;
    yield_point().await;
    yield_point().await;
    yield_point().await;
    yield_point().await;
    yield_point().await;
    yield_point().await;
    yield_point().await;
    yield_point().await;
    yield_point().await; // 30

    yield_point().await;
    yield_point().await;
    yield_point().await;
    yield_point().await;
    yield_point().await;
    yield_point().await;
    yield_point().await;
    yield_point().await;
    yield_point().await;
    yield_point().await; // 40

    yield_point().await;
    yield_point().await;
    yield_point().await;
    yield_point().await;
    yield_point().await;
    yield_point().await;
    yield_point().await;
    yield_point().await;
    yield_point().await;
    yield_point().await; // 50

    yield_point().await;
    yield_point().await;
    yield_point().await;
    yield_point().await;
    yield_point().await;
    yield_point().await;
    yield_point().await;
    yield_point().await;
    yield_point().await;
    yield_point().await; // 60

    yield_point().await;
    yield_point().await;
    yield_point().await;
    yield_point().await;
    yield_point().await;
    yield_point().await;
    yield_point().await;
    yield_point().await;
    yield_point().await;
    yield_point().await; // 70

    yield_point().await;
    yield_point().await;
    yield_point().await;
    yield_point().await;
    yield_point().await;
    yield_point().await;
    yield_point().await;
    yield_point().await;
    yield_point().await;
    yield_point().await; // 80

    yield_point().await;
    yield_point().await;
    yield_point().await;
    yield_point().await;
    yield_point().await;
    yield_point().await;
    yield_point().await;
    yield_point().await;
    yield_point().await;
    yield_point().await; // 90

    yield_point().await;
    yield_point().await;
    yield_point().await;
    yield_point().await;
    yield_point().await;
    yield_point().await;
    yield_point().await;
    yield_point().await;
    yield_point().await;
    yield_point().await; // 100

    drop(a);
    drop(b);
    drop(c);
}

fn main() {}
