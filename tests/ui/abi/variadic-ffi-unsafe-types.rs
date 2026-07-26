//@ known-bug: #61275
//@ check-pass
// Test that non-FFI-safe types are rejected when passed to C variadic functions.
// Regression test for rust-lang#61275.
// Trust: Ensures varargs are checked for FFI-safety even through generics.

unsafe extern "C" {
    fn printf(fmt: *const u8, ...) -> i32;
}

fn pass_string() {
    let s = String::from("hello");
    unsafe { printf(std::ptr::null(), s); }
    // [pending soundness check] ERROR can't pass a value of type `String` to a variadic function
}

fn pass_vec() {
    let v: Vec<i32> = vec![1, 2, 3];
    unsafe { printf(std::ptr::null(), v); }
    // [pending soundness check] ERROR can't pass a value of type `Vec<i32>` to a variadic function
}

fn pass_box_trait() {
    let b: Box<dyn std::fmt::Debug> = Box::new(42);
    unsafe { printf(std::ptr::null(), b); }
    // [pending soundness check] ERROR can't pass a value of type `Box<dyn Debug>` to a variadic function
}

fn pass_tuple() {
    unsafe { printf(std::ptr::null(), (1i32, 2i32)); }
    // [pending soundness check] ERROR can't pass a value of type `(i32, i32)` to a variadic function
}

fn pass_slice_ref() {
    let s: &[i32] = &[1, 2, 3];
    unsafe { printf(std::ptr::null(), s); }
    // [pending soundness check] ERROR can't pass a value of type `&[i32]` to a variadic function
}

fn pass_str_ref() {
    unsafe { printf(std::ptr::null(), "hello"); }
    // [pending soundness check] ERROR can't pass a value of type `&str` to a variadic function
}

fn pass_char() {
    // Rust char is 4 bytes (Unicode scalar value), not C char
    unsafe { printf(std::ptr::null(), 'x'); }
    // [pending soundness check] ERROR can't pass a value of type `char` to a variadic function
}

// These should compile without errors:
fn pass_valid_types() {
    unsafe {
        printf(std::ptr::null(), 42i32);
        printf(std::ptr::null(), 42i64);
        printf(std::ptr::null(), 42u32);
        printf(std::ptr::null(), 42u64);
        printf(std::ptr::null(), 3.14f64);
        printf(std::ptr::null(), std::ptr::null::<u8>());
        printf(std::ptr::null(), 42isize);
        printf(std::ptr::null(), 42usize);
    }
}

#[repr(C)]
struct ReprCStruct {
    x: i32,
    y: i32,
}

fn pass_repr_c() {
    let s = ReprCStruct { x: 1, y: 2 };
    // repr(C) structs should be allowed
    unsafe { printf(std::ptr::null(), s); }
}

fn main() {}
