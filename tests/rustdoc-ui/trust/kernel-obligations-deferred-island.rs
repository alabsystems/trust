// Trust (TG3, COMPILE-TIME-FACTS-1): documenting a crate checks its Clean islands
// and kernel obligations as compiling it does. rustdoc runs no `analysis`, so before
// TG3 it saw only what the resolver seam checks: an island the seam cannot check — a
// deferred `trust_import_*` suffix, or one a macro introduced — went unchecked, and a
// false theorem in it documented with no diagnostic (reported by aterm's PF1 worker,
// 2026-11-05, under `targo --unverified doc`). This file is the deferred case; its twin
// kernel-obligations-macro-island.rs is the macro-introduced case. The theorem below
// is false of the imported body and must be refused.
//
//@ check-fail
//@ compile-flags: -Ztrust-verify=off

pub fn ident(x: u64) -> u64 {
    x
}

// A deferred island: it names an import, so it is checked after the body is imported.
clean {
    theorem ident_bumps (x : UInt64) : trust_import_kernel_obligations_deferred_island__ident x = x + 1 := rfl
}
//~^^ ERROR did not elaborate: Type mismatch
