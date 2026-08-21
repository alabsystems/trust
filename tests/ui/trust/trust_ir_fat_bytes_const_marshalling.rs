//@ check-pass
//@ compile-flags: -Z trust-ir-lower -Z trust-verify=off

// Trust (vtable slice 8 — oracle fat-pointer const marshalling): chain item (2) of the
// vtable campaign. The `&[u8]`/`&str` promoted-literal family was held at the LIVE-havoc
// gate UPSTREAM of the tail gate, because the MIR oracle's bridge discarded the bytes of a
// `ConstValue::Str` at any destination other than the byte-slice fat sort and emitted a
// typed fact-free `Inst::Undef` (`undef ty ptr` for `&[u8; N]` dests, `undef ty fatptr<str>`
// for `&str` dests). The bridge now mirrors the THIR producer's wave-17 convention at
// exactly those two reference shapes — a named, internal, immutable, initializer-bearing
// `__trust_bytes_*` `[u8; N]` global (+ `PtrFromParts(FatPtr(Str), addr, len)` at the fat
// dest) — and the differential's paired-global admission (slice 7) extends to:
//   * the `__trust_bytes_*` mint grammar (the per-body twin of the spliced
//     `__trust_promoted_*` names), same bit-exact content-equality conjuncts;
//   * the fat-carrier audit arm: a single-result `PtrFromParts` at a `Slice`/`Str` fat kind
//     over a tracked DATA operand is a modeled pass-through (its metadata lane is a `U64`
//     length, never an address; `TraitObject` fat kinds refuse). A tracked address in the
//     METADATA position refuses the whole function fail-closed.
//
// Every lane below is one body of the pre-registered flip population measured on
// postbuild-vtable8. Each must keep COMPILING — a lowering decline is a coverage decision,
// never an error — and each pins one arm of the marshalling.

// FAT-RETURNING &[u8] (references::FOO, byte-literals::BAR/BAZ): Str const at the thin
// `&[u8; N]` dest, unsized to the fat slice return — data lane is the paired bytes global's
// address, metadata lane the exact length.
pub const FOO: &[u8] = b"foo";
pub static BAR: &'static [u8] = b"a\xF0\t";
pub static BAZ: &'static [u8] = br"a\n";

// THIN-RETURNING &[u8; N] (byte-literals::BAR_FIXED, constref::*, mir_indexing_oob_2::C):
// the address itself is returned; the pre-slice-8 thin machinery over the bytes grammar.
pub static BAR_FIXED: &'static [u8; 3] = b"a\xF0\t";
pub const CONST_REF: &[u8; 3] = b"foo";

// FAT-RETURNING &str (issue-57280::BLAH, str-patterns::CONSTANT, module-path::name,
// macro-rules-derive::name): the producer's own LitKind::Str spelling on both sides.
pub const CONSTANT: &str = "constant";
pub fn name() -> &'static str {
    "module_path_in_nested_modules::foo::bar::baz"
}

// Behind an opaque never-read receiver (explicit-paths-pass::Trait::description,
// out-of-scope::hello, hrtb-trait-upcasting::as_str, specialization::foo_three).
pub trait Description {
    fn description(&self) -> &str {
        "hello world!"
    }
}
impl Description for () {}

// Trait-default assoc const (constref::Foo::CONST_REF_DEFAULT).
pub trait ConstRef {
    const CONST_REF_DEFAULT: &'static [u8; 3] = b"bar";
}

// Non-capturing closure returning a literal (pred-known-…::main::{closure#0}::{closure#2}).
pub fn closure_lane() -> &'static str {
    let f = || "Hello, world";
    let g = f;
    g()
}

// SCOPE PINS — must stay fail-closed declines (no bytes global, the typed Undef kept):
// a nested `&&str` (the value is a pointer to a fat pointer, NOT to the bytes — an address
// of the bytes there would be a wrong value), and the empty literal (both producers refuse
// zero-length globals).
pub const NESTED: &&str = &"nested";
pub const EMPTY: &[u8] = b"";

fn main() {}
