// Negative twin of the Lean half: a FALSE theorem beside a def in an island. The in-compiler
// Clean kernel must reject the island, so the crate must not build.
pub mod m {
    clean {
        def pick (a : UInt64) (b : UInt64) : UInt64 := a
        theorem pick_wrong (a b : UInt64) : pick a b = b := rfl
    }
}
pub fn program() -> u64 { m::pick(7, 41) }
