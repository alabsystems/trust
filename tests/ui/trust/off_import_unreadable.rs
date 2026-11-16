//@ revisions: unopt opt
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=off
//@[opt] compile-flags: -O
//@ check-fail
//@ dont-require-annotations: NOTE
//! TG3: a kernel obligation over a body the E6 lane cannot read is a HARD ERROR
//! that names the shape, with verification off as with it on — never a skipped
//! obligation. `sum_to` is a loop; the E6 readers refuse every loop (proofs
//! about real Rust loop bodies wait on Workstream C/E), so the island that
//! imports it is refused, and the error says which gate refused which
//! construct.

pub fn sum_to(n: u64) -> u64 {
    let mut acc = 0u64;
    let mut i = 0u64;
    while i < n {
        acc = acc.wrapping_add(i);
        i += 1;
    }
    acc
}

clean {
    theorem sum_to_zero : trust_import_off_import_unreadable__sum_to 0 = 0 := rfl
}
//~^^ ERROR has no checked E6 program admission
//~| ERROR `trust_import_off_import_unreadable__sum_to` names a Rust function body that cannot be imported into the Clean kernel

fn main() {
    let _ = sum_to(3);
}
