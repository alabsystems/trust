//! TINV step 0(a): entry-version binding for a `&mut` pointee, on real MIR.
//!
//! `tests/fixtures/tinv_mut_pointee_entry_rename_mir.json` is the stage-1
//! compiler's extraction (`trustc --edition 2021 --crate-type lib
//! -Ztrust-verify=on -Ztrust-dump=mir:<dir>`) of
//!
//! ```text
//! pub struct S { pub v: Vec<u8>, pub k: usize }
//! impl S {
//!     pub fn rebind(&mut self) -> u8 {
//!         let a = self.v[self.k];   // bb0[1]: _5 = copy (*_1).1
//!         self.k = self.v.len();    // bb2[0]: (*_1).1 = move _6
//!         a ^ self.v[self.k]        // bb2[2]: _11 = copy (*_1).1
//!     }
//! }
//! ```
//!
//! TINV's `&mut` entry facts (TINV-5) state the invariant over the bare pointee
//! names, which the version oracle reads as the entry value. That is sound only if
//! every read before the first write is unversioned and every read after it is
//! not: otherwise the entry `k < v.len()` would bind the post-write `k == v.len()`
//! (design §5 witness 23, out of bounds).
use trust_types::{BlockId, VerifiableFunction};

fn load() -> VerifiableFunction {
    let path = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/tests/fixtures/tinv_mut_pointee_entry_rename_mir.json"
    );
    serde_json::from_str(&std::fs::read_to_string(path).expect("fixture")).expect("deserialize")
}

#[test]
fn mut_pointee_field_read_before_write_binds_entry_and_after_write_binds_fresh() {
    let func = load();
    let sv = super::stmt_versions_for(&func);
    let at = |b: usize, k: usize, name: &str| sv.version_token_at(&func, BlockId(b), k, name);

    // The shape the assertions below are about.
    let stmt = |b: usize, k: usize| format!("{:?}", func.body.blocks[b].stmts[k]);
    assert!(stmt(0, 1).contains("local: 5") && stmt(0, 1).contains("Field(1)"), "{}", stmt(0, 1));
    assert!(stmt(2, 0).contains("local: 1") && stmt(2, 0).contains("Field(1)"), "{}", stmt(2, 0));
    assert!(stmt(2, 2).contains("local: 11") && stmt(2, 2).contains("Field(1)"), "{}", stmt(2, 2));

    for name in ["self*.1", "self*", "self"] {
        // Before the first terminator, every read is the entry version: this is
        // where a TINV `&mut` entry fact applies.
        for k in 0..=2 {
            assert_eq!(at(0, k, name), None, "{name} at bb0[{k}] must be the entry version");
        }
        // After the write, a fresh version, distinct from every earlier one: the
        // entry fact can never reach the post-write read. This is the G14 property.
        let before: Vec<_> = [(0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2), (2, 0)]
            .into_iter()
            .map(|(b, k)| at(b, k, name))
            .collect();
        for (b, k) in [(2, 1), (2, 2), (2, 3), (3, 0), (3, 1), (3, 2)] {
            let after = at(b, k, name);
            assert!(
                after.is_some(),
                "{name} at bb{b}[{k}], after `self.k = ..`, binds the entry version"
            );
            assert!(
                !before.contains(&after),
                "{name} at bb{b}[{k}] shares a pre-write version {after:?}"
            );
        }
    }
    // MEASURED, NOT REQUIRED (2026-10-05): the shared-borrow calls `Index::index(&self.v, _)`
    // and `Vec::len(&self.v)` re-version `self.v` and, through the overlapping `*self`,
    // `self.k` (`e_s0_t` at bb1, `e_s1_t` at bb2[0]). Sound, but it confines entry facts to
    // reads before the first call. A tightening may turn these into `None`; it must never
    // touch the assertions above.
}
