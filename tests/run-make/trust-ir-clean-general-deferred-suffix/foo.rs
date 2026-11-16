//! CLEAN-GENERAL-DEFERRED-1: three islands, partitioned the way the compiler partitions
//! them (`trust_certify::clean_island::pre_admission_island_count`):
//!   * island 1 names no `trust_import_*`: the PRE-ADMISSION prefix, the only
//!     islands the general trust-ir lane's environment holds;
//!   * island 2 is the first that names one (`trust_import_foo__first`, the E6
//!     program admission of `first` below): the deferred suffix starts here;
//!   * island 3 names none itself and is deferred because it follows island 2.
//! `prefixRank`, `namingRank` and `suffixRank` are one shape (an inductive
//! `match` the 13-shape planner cannot spell, as `triRank` in
//! `../trust-ir-emit-clean-origin`), so only their placement differs.

/// The Rust function island 2's theorem names through its E6 program admission.
pub fn first(a: u64, _b: u64) -> u64 {
    a
}

clean {
    inductive Tri where
      | one : Tri
      | two : Tri
      | three : Tri

    def prefixRank (t : Tri) : UInt64 :=
      match t with
      | Tri.one => 1
      | Tri.two => 2
      | Tri.three => 3
}

clean {
    theorem firstKeeps (a b : UInt64) : trust_import_foo__first a b = a := rfl

    def namingRank (t : Tri) : UInt64 :=
      match t with
      | Tri.one => 4
      | Tri.two => 5
      | Tri.three => 6
}

clean {
    def suffixRank (t : Tri) : UInt64 :=
      match t with
      | Tri.one => 3
      | Tri.two => 2
      | Tri.three => 1
}
