// Blessed env_mutation (2026-07-20): pre-existing code that predates the
// toolchain's deny-by-default ENV_MUTATION lint. Mutates process-global env
// under local save/restore, an RAII guard, or single-threaded harness/CLI
// context. Marked for later migration to a lock-scoped helper; the wall stays
// armed for all NEW code outside these marked modules. unknown_lints keeps the
// stock-toolchain build green (the lint name is Trust-only).
#![allow(unknown_lints)]
#![allow(env_mutation)]
#[no_mangle]
pub fn cold_function(c: u8) {
    println!("cold {}", c);
}

#[no_mangle]
pub fn hot_function(c: u8) {
    std::env::set_var(format!("var{}", c), format!("hot {}", c));
}

fn main() {
    let arg = std::env::args().skip(1).next().unwrap();

    for i in 0..1000_000 {
        let some_value = arg.as_bytes()[i % arg.len()];
        if some_value == b'!' {
            // This branch is never taken at runtime
            cold_function(some_value);
        } else {
            hot_function(some_value);
        }
    }
}
