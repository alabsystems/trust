//! Trust (2026-10-02): a bundle member's source identity key, computed AT MOST ONCE per member
//! per bundle stage instead of once per question.
//!
//! ## The cost this removes
//!
//! `bundled_member_source_identity_key` is asked about the SAME members from ~20 call sites while
//! one bundle is built: four ledger writes per admitted member, the survivor loop's
//! `keeps_local_member` once per survivor per round, the constructor reconciliation (whose plan
//! visits every child once per parent), the Assert gate (whose nested ownership check asks the
//! caller's key once per Assert-bearing member it calls), the `Vec` index-forwarder charge and the
//! own-row set. Every call serialized the whole member to JSON, and every miss of the
//! process-wide byte memo (`FunctionSourceDigestMemo`: 64 MiB, then it stopped remembering; T3 L4
//! C09d deleted it, so this scope is the one reuse of a key left) re-ran SHA-256 over those
//! bytes. MEASURED on trust-ir efcfb431's verified check (`targo trust check`,
//! stage-1 trustc at 6932b9c993 and b499993ce1, 17 periodic 20 s `sample` windows per lane):
//! `bundled_member_source_identity_key` held 9.7% (trust_ir lib) / 11.3% (trust_ir test) of the
//! busy samples over the whole run and up to 40% in the early windows; inside it, serialization
//! 35-38% and miss-path hashing 53-57%, i.e. 90-95% of it is paid by a release build too.
//! At t=1200 s the byte memo answered none of the repeats (0 hit samples): it had stopped
//! remembering once full.
//!
//! ## What a scope does
//!
//! [`MemberKeyScope::new`] registers a BORROWED member slice on this thread for the guard's
//! lifetime. While the guard lives, the key of a `&VerifiableFunction` that IS an element of that
//! slice (the reference points at the element's own storage) is answered from the scope's table;
//! the table computes each element's key on its first request, with the unchanged computation
//! (`compute_bundled_member_source_identity_key`). Every other reference — a clone, a fresh
//! extraction, an element of a slice no live scope registered — misses and is computed exactly as
//! before. Scopes nest (a nested bundle may be built while one is being assembled; each registers
//! its own slices) and are removed by identity when their guard drops, in any order.
//!
//! ## Why the answer is byte-identical, for every input
//!
//! A table entry is the unchanged computation applied to the element itself, so it can differ
//! from what the caller would have computed only if the element changed, or another value took
//! its place, between the entry's computation and the question. Neither can happen while the
//! guard lives. The guard holds the shared borrow `&'a [VerifiableFunction]`, so the borrow
//! checker refuses any write to, move of, or drop of the slice's storage until the guard is gone,
//! and `VerifiableFunction` has no interior mutability (no `Cell`, `RefCell`, lock, atomic or
//! lazily filled field anywhere in `trust_types`' model; the one shared carrier, `SharedVec`, is
//! an `Arc<Vec<_>>` that only a `&mut` could change). A reference whose address is the start of
//! element `i` of storage the slice occupies can only be element `i`: no other value can live
//! there while the slice does. Nothing is compared by name, path or hash; the address decides,
//! and only inside storage the guard keeps alive and immutable.
//!
//! The one way to break that is to leak a guard (`std::mem::forget`, `Box::leak`), which would
//! keep a table registered after its borrow ended. No caller does; a guard is a local that drops
//! at the end of its block or by an explicit `drop`, also on unwinding.
//!
//! A guard is also NOT `Send` (its `PhantomData<*const ()>` marker, pinned at compile time
//! below): the table lives on the registering thread's stack, and a guard dropped on another
//! thread would look for it in THAT thread's stack, leaving the table registered after the
//! borrow ended. The compiler refuses to move a guard to another thread.
//!
//! ## Auditing it
//!
//! With `TRUST_MEMBER_KEY_AUDIT=<directory>` every answer a table gives is ALSO recomputed the
//! old way, with the UNMEMOIZED digest (`compiler_function_source_digest_hex`), and compared.
//! Each scope appends one summary row to `<directory>/member-key-audit-<pid>.tsv` when it drops,
//! and every mismatch a `MISMATCH` row at once. Diagnostic only: it changes no answer, and the
//! audit writes nowhere but that directory.

use std::cell::{Cell, OnceCell, RefCell};
use std::marker::PhantomData;

use super::{
    BundledMemberSourceIdentityKey, compiler_function_source_digest_hex,
    compute_bundled_member_source_identity_key,
};

#[cfg(test)]
mod tests;

/// One registered slice: where its elements live, and each element's key once asked.
struct Table {
    id: u64,
    base: usize,
    len: usize,
    keys: Box<[OnceCell<Result<BundledMemberSourceIdentityKey, String>>]>,
    answered: Cell<usize>,
    computed: Cell<usize>,
    audited: Cell<usize>,
    mismatches: Cell<usize>,
}

impl Table {
    /// The index of the element whose storage starts at `address`, if one does.
    fn index_of(&self, address: usize) -> Option<usize> {
        let size = std::mem::size_of::<trust_types::VerifiableFunction>();
        let offset = address.checked_sub(self.base)?;
        if offset % size != 0 {
            return None;
        }
        let index = offset / size;
        (index < self.len).then_some(index)
    }
}

thread_local! {
    static TABLES: RefCell<Vec<Table>> = const { RefCell::new(Vec::new()) };
    static NEXT_TABLE_ID: Cell<u64> = const { Cell::new(0) };
    /// Questions no live table could answer since the last audit row (audit only).
    static UNSCOPED_SINCE_LAST_ROW: Cell<usize> = const { Cell::new(0) };
}

static AUDIT_DIRECTORY: std::sync::LazyLock<Option<std::path::PathBuf>> =
    std::sync::LazyLock::new(|| {
        std::env::var_os("TRUST_MEMBER_KEY_AUDIT")
            .filter(|value| !value.is_empty())
            .map(std::path::PathBuf::from)
    });

fn audit_append(row: &str) {
    use std::io::Write as _;
    let Some(directory) = &*AUDIT_DIRECTORY else {
        return;
    };
    let path = directory.join(format!("member-key-audit-{}.tsv", std::process::id()));
    if let Ok(mut file) = std::fs::OpenOptions::new().create(true).append(true).open(path) {
        // ONE write per row, newline included: `writeln!` on an unbuffered `File` writes the
        // row and the newline separately, so rows from threads auditing at once could
        // interleave (seen in review: `unscoped_since_last=0SCOPE\t...` on one line), and a
        // `MISMATCH` row glued to another row would be miscounted by a line-based reader.
        // Diagnostic only: a failed write loses an audit row, never an answer.
        let _ = file.write_all(format!("{row}\n").as_bytes());
    }
}

/// The guard of one registered slice. See the module documentation.
#[must_use = "a scope answers only while its guard is alive"]
pub(super) struct MemberKeyScope<'a> {
    id: u64,
    _members: PhantomData<&'a [trust_types::VerifiableFunction]>,
    /// Not `Send`: the guard must drop on the thread whose stack holds its table.
    _not_send: PhantomData<*const ()>,
}

// Compile-time pin that `MemberKeyScope` is not `Send`: were it `Send`, both impls below would
// apply and `some_item` would be ambiguous (E0283), so this item would not compile.
const _: fn() = || {
    trait AmbiguousIfSend<A> {
        fn some_item() {}
    }
    impl<T: ?Sized> AmbiguousIfSend<()> for T {}
    impl<T: ?Sized + Send> AmbiguousIfSend<u8> for T {}
    let _ = <MemberKeyScope<'static> as AmbiguousIfSend<_>>::some_item;
};

impl<'a> MemberKeyScope<'a> {
    /// Register `members` on this thread until the guard drops. Computes nothing yet: each
    /// element's key is computed on its first request.
    pub(super) fn new(members: &'a [trust_types::VerifiableFunction]) -> Self {
        let id = NEXT_TABLE_ID.with(|next| {
            let id = next.get();
            next.set(id.wrapping_add(1));
            id
        });
        let table = Table {
            id,
            base: members.as_ptr().addr(),
            len: members.len(),
            keys: members.iter().map(|_| OnceCell::new()).collect(),
            answered: Cell::new(0),
            computed: Cell::new(0),
            audited: Cell::new(0),
            mismatches: Cell::new(0),
        };
        TABLES.with(|tables| tables.borrow_mut().push(table));
        MemberKeyScope { id, _members: PhantomData, _not_send: PhantomData }
    }

    /// `(answered, computed)` by this scope's table so far (tests).
    #[cfg(test)]
    pub(super) fn counts(&self) -> (usize, usize) {
        TABLES.with(|tables| {
            let tables = tables.borrow();
            let table = tables.iter().find(|table| table.id == self.id).expect("live scope");
            (table.answered.get(), table.computed.get())
        })
    }
}

impl Drop for MemberKeyScope<'_> {
    fn drop(&mut self) {
        let removed = TABLES.with(|tables| {
            let mut tables = tables.borrow_mut();
            let position = tables.iter().position(|table| table.id == self.id)?;
            Some(tables.remove(position))
        });
        if let Some(table) = removed
            && AUDIT_DIRECTORY.is_some()
            && table.answered.get() > 0
        {
            let unscoped = UNSCOPED_SINCE_LAST_ROW.with(|count| count.replace(0));
            audit_append(&format!(
                "SCOPE\tmembers={}\tanswered={}\tcomputed={}\taudited={}\tmismatches={}\t{}={}",
                table.len,
                table.answered.get(),
                table.computed.get(),
                table.audited.get(),
                table.mismatches.get(),
                "unscoped_since_last",
                unscoped,
            ));
        }
    }
}

/// The key of `member` from the innermost live table whose slice holds it, or `None` when no
/// live table does (the caller then computes it as before).
pub(super) fn scoped_key(
    member: &trust_types::VerifiableFunction,
) -> Option<Result<BundledMemberSourceIdentityKey, String>> {
    let address = std::ptr::from_ref(member).addr();
    let answer = TABLES.with(|tables| {
        let tables = tables.borrow();
        let (table, index) =
            tables.iter().rev().find_map(|table| Some((table, table.index_of(address)?)))?;
        let key = table.keys[index]
            .get_or_init(|| {
                table.computed.set(table.computed.get() + 1);
                compute_bundled_member_source_identity_key(member)
            })
            .clone();
        table.answered.set(table.answered.get() + 1);
        if AUDIT_DIRECTORY.is_some() {
            table.audited.set(table.audited.get() + 1);
            if !answer_matches_old_computation(member, &key) {
                table.mismatches.set(table.mismatches.get() + 1);
            }
        }
        Some(key)
    });
    if answer.is_none() && AUDIT_DIRECTORY.is_some() {
        UNSCOPED_SINCE_LAST_ROW.with(|count| count.set(count.get() + 1));
    }
    answer
}

/// Audit: is `answer` exactly what the pre-scope code returned for `member`, recomputed with the
/// UNMEMOIZED digest? A mismatch is written out at once.
fn answer_matches_old_computation(
    member: &trust_types::VerifiableFunction,
    answer: &Result<BundledMemberSourceIdentityKey, String>,
) -> bool {
    let old = old_computation(member);
    let matches = same_answer(answer, &old);
    if !matches {
        let digest = |key: &Result<BundledMemberSourceIdentityKey, String>| match key {
            Ok(key) => key.source_digest.clone(),
            Err(error) => format!("error: {error}"),
        };
        audit_append(&format!(
            "MISMATCH\tdef_path={}\tscoped={}\told={}",
            member.def_path,
            digest(answer),
            digest(&old)
        ));
    }
    matches
}

/// Audit: the key the code before scopes returned for `member`, over the UNMEMOIZED digest.
fn old_computation(
    member: &trust_types::VerifiableFunction,
) -> Result<BundledMemberSourceIdentityKey, String> {
    compiler_function_source_digest_hex(member).map(|source_digest| {
        BundledMemberSourceIdentityKey {
            name: member.name.clone(),
            def_path: member.def_path.clone(),
            source_digest,
        }
    })
}

/// Audit: is a table's `answer` the `old` computation's? Pure, so a test can check that the
/// audit flags a wrong answer without writing an audit row.
fn same_answer(
    answer: &Result<BundledMemberSourceIdentityKey, String>,
    old: &Result<BundledMemberSourceIdentityKey, String>,
) -> bool {
    match (answer, old) {
        (Ok(answer), Ok(old)) => answer == old,
        // Both failed: the old code returned an error too (the message names the same path).
        (Err(_), Err(_)) => true,
        _ => false,
    }
}
