// RANK 3 (fail-safe): offset_of! desugars to a nested anon-const child body the
// root-body checker never walks, and offset_of_data is never encoded. Pre-fix,
// the root ACCEPTed, then thir_body of the child const unwrapped the empty
// offset_of_data map -> hard ICE (exit 101). Expected post-fix: mintable()
// excludes offset_of! roots, warm replay is a clean MISS, output byte-identical
// to a no-flag build (no ICE).
#[repr(C)]
pub struct S {
    pub a: u32,
    pub b: u64,
}

pub fn off_b() -> usize {
    core::mem::offset_of!(S, b)
}
