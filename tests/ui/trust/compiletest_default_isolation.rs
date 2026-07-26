//@ check-pass
//@ compile-flags: --crate-type=lib

// Ordinary UI tests exercise compiler semantics and must not accidentally become
// verifier conformance tests. Union projection is intentionally useful here: the
// batteries-on verifier rejects this currently unsupported lowering, while vanilla
// Rust compilation accepts it. Compiletest's Trust capability should add the opt-out.

pub union Word {
    left: u32,
    right: u32,
}

pub unsafe fn read_left(word: Word) -> u32 {
    unsafe { word.left }
}
