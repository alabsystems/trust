// Trust: Regression test for rust-lang#130521
// Calling a function with a packed struct field as the destination
// should not ICE in MIR validation. The compiler must use an aligned
// temporary for the call result, then copy to the packed field.
//
//@ check-pass

#[repr(packed)]
struct Packed {
    x: u8,
    data: String,
}

fn make_string() -> String {
    String::from("hello")
}

fn main() {
    let mut p = Packed { x: 0, data: String::new() };
    // This assignment involves a call (String::from) whose result goes
    // to a packed struct field. Without the fix, MIR validation ICEs
    // because the call destination is potentially unaligned.
    p.data = make_string();
    assert_eq!(unsafe { &*std::ptr::addr_of!(p.data) }, "hello");
}
