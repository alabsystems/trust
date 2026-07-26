// Trust test: remainder by zero -- safe variant
// VcKind: RemainderByZero
// Expected: RemainderByZero PROVED (guard proves the divisor is nonzero)
// Safe pattern: if-guard `y == 0` returns fallback before remainder
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

fn modulo_safe(x: u32, y: u32) -> u32 {
    if y == 0 {
        0 // fallback for zero divisor
    } else {
        x % y // SAFE: guard ensures y != 0
    }
}

fn main() {
    let _ = modulo_safe(10, 3);
    let _ = modulo_safe(10, 0); // takes fallback branch
}
