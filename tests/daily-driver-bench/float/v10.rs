pub fn f(a: f32, b: f32) -> f32 requires a <= 1.0 && a >= -1.0 && b <= 1.0 && b >= -1.0 { a + b }
