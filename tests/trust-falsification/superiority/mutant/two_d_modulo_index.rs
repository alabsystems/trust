#![crate_type = "lib"]
// MUTANT of proved/two_d_modulo_index.rs: `i % 5` reaches 4 on the outer 4-row
// matrix -> OUT OF BOUNDS row. MUST be refused (exit 1).
pub fn two_d_modulo_index(m: &[[u32; 4]; 4], i: usize, j: usize) -> u32 {
    m[i % 5][j % 4]
}
