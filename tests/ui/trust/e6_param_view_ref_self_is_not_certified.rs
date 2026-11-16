//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! ref-self I1 — the borrow-erased E6 PARAMETER VIEW, and the ONE thing about
//! it owner ruling R1 made non-negotiable: **the row it discharges is NOT
//! reported `Certified`.**
//!
//! What the lane does. `x_ref(&self) -> u32 { self.x }` has no E6 facets today:
//! `facet_inference::local_ty_in_closed_fragment` refuses every `Ty::Ref`-typed
//! local, so nothing on it can cite Lean. `trust_types::e6_param_view` builds a
//! borrow-erased COPY of the extracted body in which `Point`'s scalar fields are
//! by-value parameters named `self.x` and `self.y`; the UNCHANGED validator,
//! recognizer and mint then run on the copy. No refusal is edited.
//!
//! What that costs, disclosed here because this is the file a reader reaches
//! for. The Clean-side defining equation is a function of the pointee's field
//! VALUES AT ENTRY. That those values are what the function reads is an
//! ASSUMPTION — a live `&T` argument with `T: Freeze` is dereferenceable and its
//! pointee is immutable for the duration of the call — accepted as owner ruling
//! R1 (2026-09-17) and carried as the `EnsuresCitationViewDischarge` row in
//! `docs/TCB.md`. So:
//!
//!   * the per-function note says `view: frozen-shared-erased` and does NOT
//!     count this row in `of which N kernel-certified`;
//!   * the sealed authority grades it `Trusted`/`Constructive`;
//!   * `-Ztrust-dump=spec-clean` writes `"view": "frozen-shared-erased"` on the
//!     goal row, and `null` on the by-value twin's;
//!   * the wire row carries the distinct solver label `clean-kernel-view-*` and
//!     NO kernel proof evidence at all, which is what makes the authenticated
//!     `targo trust` lane withhold it.
//!
//! **Why `check-pass` is not vacuous.** `-Ztrust-verify=on` is strict, and a
//! clause that calls a Clean island definition is outside every solver lane's
//! vocabulary (its rows are fail-closed `SpecEnsuresUnparseable` sentinels), so
//! the only thing that can close these rows is the kernel discharge this
//! fixture exists for. Before the increment `x_ref` and its siblings did not
//! compile under this flag at all. The close negatives live in
//! `e6_param_view_refusals_say_why.rs`.

// `id32_two` is shaped for the VIEW's arity: the goal for `y_ref` is
// `forall (self.x) (self.y), <import y_ref> self.x self.y = id32 self.y`, the
// same shape `wadd_self` proves for the by-value `add2` in
// `e9_cited_island_def_discharge.rs`. (`//` is not a comment inside an island,
// so this note lives outside it.)
clean {
    def id32 (x : UInt32) : UInt32 := x
    theorem id32_two : forall (a b : UInt32), id32 b = id32 b := fun a b => rfl
    theorem id32_one : forall (a : UInt32), id32 a = id32 a := fun a => rfl
}

pub struct Point {
    pub x: u32,
    pub y: u32,
}

// Same DECLARED field shape as `core::cell::UnsafeCell<u32>` — one field, a
// `u32`. This is the positive half of the `Freeze` differential: the negative
// (`cell_peek` in the refusals fixture) differs from it only in interior
// mutability, which is what `is_freeze` refuses and what nothing else in this
// increment would.
pub struct Boxed {
    pub value: u32,
}

impl Point {
    // THE POSITIVE, UNCITED (island definitional equality). `self.x` is spelled
    // exactly as it is on a by-value `self` — the parameter view needed no
    // elaborator change for it, which was measured, not assumed
    // (`trust_spec_elab::machine_domain_tests::a_view_import_denotes_result_in_its_own_ensures`).
    pub fn x_ref(&self) -> u32
        ensures result == id32(self.x)
    {
        self.x
    }

    // THE POSITIVE, CITED. This is the route the whole two-language surface is
    // for — a Rust contract that CITES a Lean theorem — and it is the one the
    // post-walk CITATION SWEEP grades. The sweep reads the SESSION environment
    // and facet table, not the per-body clones the in-walk lane builds, so
    // without the session view mint this function discharged in the walk and
    // then hard-errored in the sweep on the row the compiler had just proved.
    // That contradiction is exactly what this function pins closed.
    pub fn y_ref(&self) -> u32
        ensures result == id32(self.y) by id32_two
        //~^ NOTE kernel-discharges this postcondition statement
    {
        self.y
    }

    // THE REGRESSION TWIN for the binder table. A frozen shared parameter now
    // contributes `self.x` / `self.y` rows to `trust_fn_param_type_names`, and
    // this clause mentions NEITHER — it is a result-free fact about `n` alone.
    // `discharge_used_bindings` filters the ∀-closure to the clause's own free
    // variables, so the goal is still `∀ n, id32 n = id32 n` and the cited
    // theorem still inhabits it. If the added rows ever reached the closure,
    // this function goes red while nothing else in the suite moves.
    pub fn gap(&self, n: u32) -> u32
        ensures id32(n) == id32(n) by id32_one
        //~^ NOTE kernel-discharges this postcondition statement
    {
        n
    }
}

impl Boxed {
    // The `Freeze` differential's positive half: one declared `u32` field,
    // admitted.
    pub fn peek(&self) -> u32
        ensures result == id32(self.value)
    {
        self.value
    }
}

// THE CONTROL. No borrow anywhere: this discharges exactly as it did before the
// increment, at `Certified`, with a `null` view on its spec-clean row.
pub fn x_val(c: Point) -> u32
    ensures result == id32(c.x)
{
    c.x
}

fn main() {}
