//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=off
//@ check-fail
//@ dont-require-annotations: NOTE
//! TG16: the ODT namespace reservation in the DEFERRED lane. An island that names
//! a `trust_import_*` constant is checked after the bodies it names are imported
//! (`CleanIslandSession::check`, the sequential lane), which is also after the
//! ODT reader generated its aliases. Squatting `trust_type_*` there is refused at
//! the declaration with the namespace named, not reported as a generic duplicate.

pub fn ident(x: u64) -> u64 {
    x
}

clean {
    theorem trust_type_ident_fact (x : UInt64) :
        trust_import_clean_island_reserved_odt_namespace_deferred__ident x = x := rfl
}
//~^^^ ERROR declares into the compiler's ODT readable-alias namespace (`trust_type_*`)

fn main() {
    let _ = ident(1);
}
