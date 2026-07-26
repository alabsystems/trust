//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ dont-check-compiler-stderr
//@ build-pass

pub fn safe_div(x: i32, y: i32) -> i32 {
    if y != 0 && !(x == i32::MIN && y == -1) {
        x / y
    } else {
        0
    }
}

pub fn safe_shift(x: u32, amount: u32) -> u32 {
    if amount < 32 {
        x << amount
    } else {
        0
    }
}

fn main() {
}
