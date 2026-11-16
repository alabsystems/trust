//! Trust (X1, 2026-09-23): WHICH foreign destructors may be admitted into a
//! native bundle as drop-glue CREDIT.
//!
//! # The silent false proof this closes
//!
//! `admit_foreign_destructor` (in `trust_verify.rs`) puts a foreign ADT's
//! `<T as Drop>::drop` into the bundle and records `T` in
//! `ADMITTED_DESTRUCTOR_ADTS`. That set reaches the bridge as
//! `bundled_destructor_adts`, and `is_panic_free_drop_ext` /
//! `drop_glue_variant_licence` then treat `T`'s drop glue as PANIC-FREE: the drop
//! lowers to `Assert(true)` and never calls the destructor body. The destructor
//! body is a bundle MEMBER, and a member's panic is demanded of nobody (the
//! `docs/TCB.md` "A bundled member's `Assert` mints NO obligation" class). So the
//! credit is not "the destructor was checked" — it is "the destructor is
//! believed".
//!
//! For the sysroot that belief is the disclosed sysroot TCB: `core`/`alloc`/`std`
//! (and the sysroot-internal crates they are built from, `hashbrown` among them)
//! are compiled verify-off by bootstrap and trusted on every path. For a
//! DEPENDENCY it is a false proof. Measured on stage-1 `trustc` at `fa6661d85e`,
//! a verify-off rlib built `-Zalways-encode-mir` (what `targo` injects into every
//! unit) with
//!
//! ```text
//! pub struct B(pub u32);
//! impl Drop for B { fn drop(&mut self) { if self.0 == 7 { panic!("boom") } } }
//! ```
//!
//! and a verifying binary doing `drop(dropdep::B(7))` built rc=0 with ZERO
//! warnings ("1 proved" twice) and the binary exited 101. The same shape through
//! `Some(B)`, `(B, u8)`, `((B,),)`, `[B; 1]`, `Result<B, u8>`, `RefCell<B>` and
//! `Cell<Option<B>>` did the same. Controls: the same dependency WITHOUT encoded
//! MIR refused every one of them (the destructor is then not admitted, so the
//! member's drop-glue row stays fail-closed), and so did a local copy.
//!
//! The scope-end drop (`let g = dep::B(x); g.0`) was already refused — but only
//! by `body_drops_foreign_adt_argument`, a ROOT-body check; the glue credit
//! itself was granted there too. A drop that happens inside a bundled sysroot
//! member (`core::mem::drop::<dep::B>`) is invisible to that root check, which
//! is why `drop(g)` leaked.
//!
//! # The rule
//!
//! A destructor is admitted as credit only when its defining crate is part of
//! the compiler's own sysroot, authenticated WITHOUT trusting a crate name:
//!
//!  * `crate_is_authentic_foundational` — lang-item ownership (`core`/`alloc`/
//!    `std`), which also holds while bootstrap builds the sysroot itself; or
//!  * `trust_mir_extract::def_is_in_sysroot_resident_crate` — every artifact the
//!    loader opened sits in this compiler's own target library directory. This
//!    keeps the existing credit for the sysroot-internal `hashbrown::raw::
//!    RawTable` (measured: `drop(HashMap<u8, u8>)` admits it today).
//!
//! Everything else — a crates.io dependency, a workspace sibling, a crate in the
//! declared bundling scope (`-Ztrust-bundle-foreign-crate`), a crate that merely
//! calls itself `std` — declines, exactly as if its MIR were absent. That is
//! the pre-existing fail-closed path: the member's drop of `T` keeps its
//! `[trust-drop-glue-assumption]` row, which the default policy refuses.
//!
//! AND the sysroot crate's NAME must be unshadowed: the credit reaches the
//! bridge as a rendered path string, so a dependency (or the local crate) that
//! shares a sysroot crate's name — `hashbrown` is an ordinary crates.io name —
//! would otherwise inherit the sysroot type's credit for its own same-path type
//! (adversarial review, 2026-09-23; measured in `foreign_destructor_may_be_credited`).
//!
//! Trust (DROP-NAME-COLLIDE-1, 2026-10-03): that hole was never specific to the
//! sysroot. EVERY drop-glue credit reaches the bridge as a rendered path, and the
//! structural set (`collect_structural_drop_adts`) is the bigger writer: a local
//! `foo::Conn` whose `Drop` proved total (or that has none) credited a
//! dependency's same-path `foo::Conn` whenever two crates shared the name `foo` —
//! Cargo's bin+lib layout, or two versions of one crate. Measured BEFORE on a
//! stage 1 whose drop-credit code matches `d5da8dc314`: certify rc=0, 3/3
//! functions verified, and the binary exited 101 in the dependency's `drop`
//! (docs/KNOWN_HAZARDS.md, DROP-NAME-COLLIDE-1). So the name test is now ONE
//! helper, `trust_mir_extract::crate_name_is_shared`, read here (with this rule's
//! sysroot-credited exemption), by the structural collection (no exemption: a
//! shared-name crate's ADT paths are withheld from the two NAME-keyed credits,
//! the structural set and the bundled-destructor set derived from this module's
//! admissions; the extraction stamp `AdtAuth::TotalDrop`, computed per concrete
//! type, still credits) and by the extractor's callee disambiguation.
//! Pinned by `tests/ui/trust/drop_credit_crate_name_collision.rs` and, for what
//! the withdrawal must NOT take, `drop_credit_crate_name_shared_stamp_kept.rs`.
//!
//! Trust (2026-09-29): a sysroot destructor that, at the concrete type, can reach
//! code outside the sysroot — a function pointer or `dyn` pointee the value
//! carries, a dependency type or allocator it drops or calls — is still admitted
//! as a member (its body's own rows stay) but is NOT credited: the drop-reach
//! walk (`sysroot_drop_reach`, recorded by `record_body_drop_reach`) withdraws its
//! path from `bundled_destructor_adts` and from every name-keyed arm of the
//! bridge. The sysroot TCB is a belief about the sysroot's code, not about the
//! code a dropped value hands it.
//!
//! # What this deliberately does NOT do
//!
//! It does not re-derive the dependency's destructor. A sound lane for that
//! exists — `drop_glue_discharges_panic_freedom` verifies `<T as Drop>::drop` in
//! THIS compilation when the crate is in the declared bundling scope — but
//! crediting through it here would be a widening, and the D4 decision owns that
//! widening. This module only narrows: its output is a subset of what was
//! admitted before, so no verdict can move from refused to verified.
//!
//! Pinned by `tests/ui/trust/xcrate_drop_glue_dep_destructor_not_credited.rs`
//! and `tests/ui/trust/xcrate_drop_glue_sysroot_name_shadowed_not_credited.rs`.

use rustc_middle::ty::TyCtxt;
use rustc_span::def_id::DefId;

/// May the destructor `destructor_did` (a foreign `<T as Drop>::drop`) be
/// admitted into a native bundle, and so CREDIT `T`'s drop glue?
///
/// `true` only for a destructor defined in the compiler's own sysroot. Every
/// uncertain answer is `false` (decline = keep the fail-closed drop-glue row).
pub(super) fn foreign_destructor_may_be_credited(tcx: TyCtxt<'_>, destructor_did: DefId) -> bool {
    // A local destructor is never admitted by this lane (the caller returns
    // before asking); answer `false` so a future caller cannot mistake this for
    // a local grant.
    if destructor_did.is_local() {
        return false;
    }
    let krate = destructor_did.krate;
    if !crate_is_sysroot_credited(tcx, krate) {
        declined(tcx, destructor_did, "from a non-sysroot crate");
        return false;
    }
    // The credit is keyed by the RENDERED ADT path (`hashbrown::raw::RawTable`),
    // which spells the crate NAME, not its `CrateNum`, and the bridge matches the
    // dropped type by that same string. So admitting a genuine sysroot
    // destructor also credits every OTHER type in this compilation that renders
    // to the same path. Measured on stage-1 `trustc` at `fa6661d85e` (the
    // dependency built WITHOUT MIR, i.e. exactly what this module's rule makes of
    // it): a verify-off rlib built `--crate-name hashbrown` with
    // `pub mod raw { pub struct RawTable(pub u32) }` whose `Drop` panics on 7,
    // dropped by `drop(g)` in the same function as a real `drop(HashMap)`, built
    // rc=0 and exited 101; without the `HashMap` it was refused. So a sysroot
    // crate's destructor is credited only while no crate OUTSIDE the credited
    // set (a dependency, or the local crate) shares its name. `hashbrown`,
    // `libc`, `memchr`, `object`, `gimli`, ... are ordinary crates.io names, so
    // this costs the credit whenever a program also depends on its namesake —
    // fail-closed, never a false proof.
    // Trust (DROP-NAME-COLLIDE-1, 2026-10-03): the rule is the shared
    // `trust_mir_extract::crate_name_is_shared` — the one the extractor's callee
    // disambiguation and the structural drop-credit collection
    // (`collect_structural_drop_adts`) also read, so the three cannot drift. The
    // exemption is this rule's own and only this rule's: a namesake that is itself
    // sysroot-credited does not shadow. The helper never exempts the local crate.
    // Trust (merge 2026-10-14): read through `sysroot_crate_name_is_shadowed`,
    // which delegates to that shared rule.
    if sysroot_crate_name_is_shadowed(tcx, krate) {
        declined(tcx, destructor_did, "whose crate name another, non-sysroot crate also uses");
        return false;
    }
    true
}

/// Trust (2026-10-08, review rounds 73-74): the sysroot destructors whose
/// credit is AUDITED, by the exact rendered path of the ADT that owns the `Drop`.
///
/// Admission used to credit EVERY sysroot destructor whose MIR was available, on
/// the theory that the sysroot is in the base. But the credit means "this glue
/// cannot panic", and a sysroot `Drop` can run USER code:
/// - `Waker`/`LocalWaker` call a user vtable function;
/// - `core::mem::DropGuard<T, F>` calls the user's `FnOnce`;
/// - `ThinBox<T>` and `mpmc::Receiver<T>` drop a `T` that the bridge's field walk
///   never reaches;
/// - `BinaryHeap`'s `PeekMut` calls the user's `Ord`.
///
/// All of these were PROVED under `certify` and panicked at run time, so the
/// default is now to decline. Every entry below drops only what its fields own and
/// frees through its allocator, which the bridge requires to be `Global`. The
/// guard types nested in those destructors are listed too. The list is what
/// `TRUST_DROP_GATE_DEBUG`'s `[DROP_DERIVE]` reported over both ordinary-Rust
/// sweeps and the drop fixtures, plus the `Rc`/`Arc` and hash-iterator siblings.
/// `core::io::error` is deliberately absent: `Repr` keeps a `Box<Custom>` holding
/// a user `dyn Error` behind a tagged pointer that no field walk sees. So is
/// hashbrown's `RawIntoIter`, whose allocator sits in a field named `allocation`
/// that the bridge's `Global`-allocator check does not read (std's hash iterators
/// are credited as whole `TotalDrop`-stamped types instead).
///
/// Being listed is necessary, not sufficient: `admit_foreign_destructor` also
/// requires every type parameter of the owner to be visible through its fields,
/// checked on the generic identity, so a guard holding its data behind `&mut`
/// is declined whatever it is instantiated at.
pub(super) fn sysroot_destructor_owner_is_audited(tcx: TyCtxt<'_>, adt_did: DefId) -> bool {
    const AUDITED: &[&str] = &[
        "alloc::boxed::Box",
        "alloc::raw_vec::RawVec",
        "alloc::vec::Vec",
        "alloc::vec::Vec<T, A>::dedup_by::FillGapOnDrop",
        "alloc::vec::Vec<T, A>::retain_mut::PanicGuard",
        "alloc::vec::set_len_on_drop::SetLenOnDrop",
        "alloc::vec::drain::Drain",
        "<alloc::vec::drain::Drain<'_, T, A> as core::ops::drop::Drop>::drop::DropGuard",
        "alloc::vec::into_iter::IntoIter",
        "<alloc::vec::into_iter::IntoIter<T, A> as core::ops::drop::Drop>::drop::DropGuard",
        "alloc::string::Drain",
        "alloc::rc::Rc",
        "alloc::rc::Weak",
        "alloc::rc::UniqueRc",
        "alloc::sync::Arc",
        "alloc::sync::Weak",
        "alloc::sync::UniqueArc",
        "alloc::collections::btree::map::BTreeMap",
        "alloc::collections::btree::map::IntoIter",
        concat!(
            "<alloc::collections::btree::map::IntoIter<K, V, A> as core::ops::",
            "drop::Drop>::drop::DropGuard",
        ),
        "alloc::collections::btree::mem::replace::PanicGuard",
        concat!(
            "alloc::collections::btree::node::Handle<alloc::collections::btree::",
            "node::NodeRef<alloc::collections::btree::node::marker::Dying, K, V, ",
            "NodeType>, alloc::collections::btree::node::marker::KV>::",
            "drop_key_val::Dropper",
        ),
        "alloc::collections::vec_deque::VecDeque",
        "<alloc::collections::vec_deque::VecDeque<T, A> as core::ops::drop::Drop>::drop::Dropper",
        "alloc::collections::vec_deque::drain::Drain",
        concat!(
            "<alloc::collections::vec_deque::drain::Drain<'_, T, A> as core::ops::",
            "drop::Drop>::drop::DropGuard",
        ),
        concat!(
            "<alloc::collections::vec_deque::into_iter::IntoIter<T, A> as core::",
            "iter::traits::iterator::Iterator>::try_fold::Guard",
        ),
        "alloc::collections::linked_list::LinkedList",
        concat!(
            "<alloc::collections::linked_list::LinkedList<T, A> as core::ops::",
            "drop::Drop>::drop::DropGuard",
        ),
        "core::array::Guard",
        "core::array::drain::Drain",
        "core::array::iter::IntoIter",
        "core::array::iter::iter_inner::PolymorphicIter",
        "hashbrown::raw::RawTable",
        "hashbrown::raw::RawDrain",
    ];
    let path = trust_mir_extract::safe_def_path_str(tcx, adt_did);
    if AUDITED.contains(&path.as_str()) {
        return true;
    }
    if super::env_flag_enabled("TRUST_DROP_GATE_DEBUG") {
        eprintln!(
            "[DROP_ADMIT] declined destructor of `{path}`: not on the audited sysroot \
             destructor list, so its drop glue stays fail-closed"
        );
    }
    false
}

/// Does a crate OUTSIDE the credited sysroot set — a dependency, or the local
/// crate — share `krate`'s name? Any authority keyed by a RENDERED path, which
/// spells the crate name and not its `CrateNum`, must decline a sysroot crate
/// whose name is shadowed this way; see [`foreign_destructor_may_be_credited`]
/// for the measured false proof.
pub(super) fn sysroot_crate_name_is_shadowed(
    tcx: TyCtxt<'_>,
    krate: rustc_span::def_id::CrateNum,
) -> bool {
    // Trust (merge 2026-10-14): delegates to the ONE duplicate-crate-name rule
    // (`trust_mir_extract::crate_name_is_shared`, DROP-NAME-COLLIDE-1) with this
    // rule's sysroot-credited exemption. For a non-local `krate` (the only kind
    // `crate_is_sysroot_credited` admits) it answers exactly what the private
    // copy did: the local crate shares the name, or a non-credited extern other
    // than `krate` does. The local crate is never a sysroot crate, so it stays
    // "shadowed" exactly as the private copy answered (fail-closed).
    krate == rustc_span::def_id::LOCAL_CRATE
        || trust_mir_extract::crate_name_is_shared(tcx, krate, |other| {
            crate_is_sysroot_credited(tcx, other)
        })
}

/// Is `krate` part of the compiler's own sysroot, authenticated without trusting
/// its name? See the module docs for the two arms. Also the crate bar of the
/// drop-glue reach walk (`sysroot_drop_reach`), so the two cannot drift.
pub(super) fn crate_is_sysroot_credited(
    tcx: TyCtxt<'_>,
    krate: rustc_span::def_id::CrateNum,
) -> bool {
    krate != rustc_span::def_id::LOCAL_CRATE
        && (super::crate_is_authentic_foundational(tcx, krate)
            || trust_mir_extract::def_is_in_sysroot_resident_crate(tcx, krate.as_def_id()))
}

fn declined(tcx: TyCtxt<'_>, destructor_did: DefId, why: &str) {
    if super::env_flag_enabled("TRUST_DROP_GATE_DEBUG") {
        eprintln!(
            "[DROP_ADMIT] declined destructor {} {why} (`{}`): an unverified Drop body \
             must not be credited, so its drop glue stays fail-closed",
            // `safe_def_path_str`, never `def_path_str`: the latter reaches
            // `trimmed_def_paths`, which ICEs a compile that emits no diagnostic.
            trust_mir_extract::safe_def_path_str(tcx, destructor_did),
            tcx.crate_name(destructor_did.krate),
        );
    }
}
