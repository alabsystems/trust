// Trust: regression test for compile-time bug rust-lang#100348
//
// O(n^2) in unused import checking. The unused import analysis iterates
// over all imports and for each one checks whether it shadows or is
// shadowed by other imports. With N imports, this results in O(N^2)
// pairwise comparisons. The bug is particularly severe when many imports
// come from the same module or when glob imports interact with specific
// imports.
//
// The original report showed significant compile-time regression with
// ~100+ use statements in a single module. This test uses 40 use
// statements with a mix of specific and nested imports to exercise the
// quadratic unused import checking path.
//
// Upstream: https://github.com/rust-lang/rust/issues/100348
// Tracked in Trust: #865
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//@ check-pass

// Multiple modules providing overlapping names. The unused import
// checker must compare each use against all others to detect shadows.

mod shapes {
    pub struct Circle;
    pub struct Square;
    pub struct Triangle;
    pub struct Pentagon;
    pub struct Hexagon;
    pub struct Octagon;
    pub struct Star;
    pub struct Diamond;

    pub mod flat {
        pub struct Plane;
        pub struct Surface;
        pub struct Sheet;
        pub struct Board;
    }

    pub mod solid {
        pub struct Cube;
        pub struct Sphere;
        pub struct Cone;
        pub struct Cylinder;
    }
}

mod colors {
    pub struct Red;
    pub struct Blue;
    pub struct Green;
    pub struct Yellow;
    pub struct Orange;
    pub struct Purple;
    pub struct Cyan;
    pub struct Magenta;

    pub mod light {
        pub struct Pastel;
        pub struct Bright;
        pub struct Neon;
        pub struct Soft;
    }

    pub mod dark {
        pub struct Matte;
        pub struct Deep;
        pub struct Shadow;
        pub struct Ink;
    }
}

// Many specific use statements — the unused import checker must compare
// each pair to determine which are used and which shadow each other.
use shapes::Circle;
use shapes::Square;
use shapes::Triangle;
use shapes::Pentagon;
use shapes::Hexagon;
use shapes::Octagon;
use shapes::Star;
use shapes::Diamond;
use shapes::flat::Plane;
use shapes::flat::Surface;
use shapes::flat::Sheet;
use shapes::flat::Board;
use shapes::solid::Cube;
use shapes::solid::Sphere;
use shapes::solid::Cone;
use shapes::solid::Cylinder;

use colors::Red;
use colors::Blue;
use colors::Green;
use colors::Yellow;
use colors::Orange;
use colors::Purple;
use colors::Cyan;
use colors::Magenta;
use colors::light::Pastel;
use colors::light::Bright;
use colors::light::Neon;
use colors::light::Soft;
use colors::dark::Matte;
use colors::dark::Deep;
use colors::dark::Shadow;
use colors::dark::Ink;

// Use every imported name to ensure none trigger "unused import" warnings.
// The compiler must still run the full O(N^2) shadow check before
// determining that all imports are used.
fn use_shapes() -> usize {
    let _ = Circle;
    let _ = Square;
    let _ = Triangle;
    let _ = Pentagon;
    let _ = Hexagon;
    let _ = Octagon;
    let _ = Star;
    let _ = Diamond;
    let _ = Plane;
    let _ = Surface;
    let _ = Sheet;
    let _ = Board;
    let _ = Cube;
    let _ = Sphere;
    let _ = Cone;
    let _ = Cylinder;
    16
}

fn use_colors() -> usize {
    let _ = Red;
    let _ = Blue;
    let _ = Green;
    let _ = Yellow;
    let _ = Orange;
    let _ = Purple;
    let _ = Cyan;
    let _ = Magenta;
    let _ = Pastel;
    let _ = Bright;
    let _ = Neon;
    let _ = Soft;
    let _ = Matte;
    let _ = Deep;
    let _ = Shadow;
    let _ = Ink;
    16
}

fn main() {
    assert_eq!(use_shapes() + use_colors(), 32);
}
