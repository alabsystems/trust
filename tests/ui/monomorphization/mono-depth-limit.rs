// Trust: Regression test for monomorphization breadth limit (rust-lang#78925, #865).
// Verifies that the compiler handles broad monomorphization (many distinct type
// instantiations of a single generic function) without hanging or excessive bloat.
//
// The tRust compiler adds a per-function instantiation limit (MONO_INSTANTIATION_LIMIT = 1024)
// in rustc_monomorphize::collector to prevent pathological cases where a single generic
// function is instantiated with thousands of distinct types, causing code bloat and
// compilation timeouts.
//
// This test exercises moderate monomorphization breadth (well under the limit) to ensure
// normal generic code compiles correctly. The actual limit is tested implicitly by the
// compiler's internal debug assertions and the compile-time caps.

//@ build-pass

// A generic function that will be instantiated with multiple types.
fn process<T: Default + std::fmt::Debug>(x: T) -> String {
    format!("{:?}", x)
}

// A trait with a generic method to test method-level monomorphization.
trait Transform {
    fn transform<U: Default + std::fmt::Debug>(&self) -> String;
}

impl Transform for i32 {
    fn transform<U: Default + std::fmt::Debug>(&self) -> String {
        format!("{}: {:?}", self, U::default())
    }
}

impl Transform for String {
    fn transform<U: Default + std::fmt::Debug>(&self) -> String {
        format!("{}: {:?}", self, U::default())
    }
}

// Nested generics that create a chain of instantiations.
fn nested_process<A: Default + std::fmt::Debug, B: Default + std::fmt::Debug>(a: A, b: B) -> String {
    let sa = process(a);
    let sb = process(b);
    format!("{} + {}", sa, sb)
}

fn main() {
    // Instantiate `process` with many distinct types (breadth).
    // This is well within the 1024 limit but exercises the breadth tracking path.
    let _ = process(0i8);
    let _ = process(0i16);
    let _ = process(0i32);
    let _ = process(0i64);
    let _ = process(0i128);
    let _ = process(0u8);
    let _ = process(0u16);
    let _ = process(0u32);
    let _ = process(0u64);
    let _ = process(0u128);
    let _ = process(0.0f32);
    let _ = process(0.0f64);
    let _ = process(false);
    let _ = process('\0');
    let _ = process(String::new());
    let _ = process(Vec::<i32>::new());
    let _ = process(Vec::<u8>::new());
    let _ = process(Vec::<String>::new());
    let _ = process(Option::<i32>::None);
    let _ = process(Option::<String>::None);
    let _ = process(Option::<Vec<i32>>::None);

    // Test method-level monomorphization breadth.
    let i = 42i32;
    let _ = i.transform::<i32>();
    let _ = i.transform::<u64>();
    let _ = i.transform::<String>();
    let _ = i.transform::<bool>();

    let s = String::new();
    let _ = s.transform::<i32>();
    let _ = s.transform::<u64>();
    let _ = s.transform::<String>();
    let _ = s.transform::<bool>();

    // Test nested generics (creates cross-product instantiations).
    let _ = nested_process(0i32, 0u32);
    let _ = nested_process(0i64, String::new());
    let _ = nested_process(String::new(), false);
    let _ = nested_process(0u8, 0.0f64);
}
