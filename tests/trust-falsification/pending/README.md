# Falsification fixtures pending an in-flight verifier capability

> **E2E CONFIRMED 2026-07-10 (the 4 session false-accept fixes).** A
> `TRUST_SEED_STAIRCASE=1 x.py build --stage 2` of the current 1.99 tree (with the
> owner's incomplete `mutual_recursive` feature temporarily stubbed in trust-vcgen
> + trust-certify, and a local `is_reserved_symbol` shim — all reverted after)
> built `rustc 1.99.0-dev (48d3ad849)` and confirmed, on the live binary:
> `str_slice_computed_byte_offset_oob` → **rc 1** (`[slice] FAILED`, the
> char-boundary fail-close); `iterator_product_overflow_silent` / `vec.sum()` /
> `str_repeat_capacity_overflow_silent` → **1 unknown, rc 0** (silent accept
> closed, drop-in preserved = the chosen runtime-checked/option-C outcome). No
> over-refutation of the safe corpus. Fixtures stay in `pending/` until the owner
> lands `Formula::FnApp` so the tree builds without the stubs. Two orthogonal
> owner findings surfaced: (a) the current tree exits rc 1 on runtime-checked /
> genuine-fatal obligations, so the safe `proved/charindices_slice_tail.rs` now
> fails via a runtime-checked `char_indices()` `[assert]` (NOT the FA fixes); (b)
> some `proved/` countdown fixtures are slow/timeout on the current tree.


These fixtures were added by commit `3cdc665129` ("verify: kill five
over-refutation classes …"). That commit **did not compile when pushed** (a
`u32`/`usize` mismatch in `rustc_mir_transform`, fixed later by `087a438b73`),
so its end-to-end falsification gate was never run. When the gate is run against
a real stage-2 `trustc`, these five fixtures do **not** hold up: two `proved/`
fixtures do not verify, one `mutant/` fixture survives, and two `mutant/`
fixtures pass only because they fail to compile. They are quarantined here —
out of the `proved/` and `mutant/` lanes the gate scans — until the in-flight
T5A / T6 / T9 verifier work that backs them lands. Each is a **capability gap
or a fixture-design error, not a soundness hole** (see per-fixture notes and the
runtime-oracle verdicts below). The sound behaviour each was meant to guard is
already covered by a sibling fixture that stays green.

This mirrors the README's "Known backend limitations (future fixtures)" policy:
a fixture the current backends cannot decide is kept **out** of the gate so the
gate does not go red for the wrong reason.

## `mutant/extern_write_unbounded_fd.rs` — survives; **NOT a fail-open**

`pub fn leak_bytes(fd, buf: *const u8, n) { unsafe { write(fd, buf, n) } }` with
an unconstrained (symbolic) `buf`. The fixture expects the `write(2)` summary's
retained `buf`-non-null demand to **refute** the call.

- **Runtime oracle:** `write(1, NULL, 5)` and `write(1, 0xdeadbeef, 5)` both
  return `-1` / `EFAULT` (errno 14), process exit `0` — **no crash, no UB**. The
  kernel validates the buffer; a bad `write` buffer is `EFAULT`, not undefined
  behaviour (contrast `strlen(NULL)` → SIGSEGV 139, which *does* refute).
- **Verifier verdict:** `0 proved, 1 unknown` (rc 0). The native trust-mc lane
  returns **Unsupported → Unknown** for the symbolic hardened-FFI-boundary
  obligation. An `unknown` obligation is an honest coverage gap under Trust's
  fail-closed doctrine (fail-closed on *refutations*; `unknown`/`timeout` are
  reported gaps, never a false proof) — the verifier never claimed the program
  safe. There is **no false proof** here.
- **Why it is not soundly refutable:** refuting a symbolic `*const u8` parameter
  passed to `write` (`buf == 0` is SAT because the caller *may* pass null) would
  reintroduce exactly the **T6 over-refutation** the *same commit* set out to
  remove, and would reject valid FFI Rust (any pointer-parameter FFI call). The
  proved sibling `proved/std_ffi_safe_paths.rs` already relies on this class
  being a non-fatal `unknown`; a blanket "hardened-FFI unknown is fatal" fix
  would turn that green fixture red.
- **Coverage preserved:** the buf-non-null demand *mechanism* is still gated by
  the sibling `mutant/write_wild_buf.rs` (a **concrete** `ptr::null()` buffer),
  which the solver refutes and which stays **green**.

## RESTORED 2026-07-07: `proved/pty_fd_seam.rs`, `proved/contract_panic_annotated.rs`, `mutant/contract_panic_unused.rs`, `mutant/contract_panic_cannot_mask.rs`

The four fixtures moved back into the gate lanes once the exact capabilities
this README asked for landed:

- **`proved/pty_fd_seam.rs`** — (1) the missing-SAFETY-comment lint now walks
  the enclosing braces up to the `unsafe {` OPENER of a multi-statement block
  (clippy `undocumented_unsafe_blocks` semantics; fail-closed brace walk in
  `unsafe_verify/detection.rs::source_has_preceding_safety_comment`), and
  (2) the sep engine structurally discharges the `[unsafe:sep:addr_of]`
  source-liveness VC for the `&mut out`-parameter FFI shape — a raw pointer of
  a whole, untracked stack local, confined to its defining block and consumed
  only as a by-value argument of that block's own call terminator, with no
  `StorageDead` of the source in between
  (`sep_engine.rs::call_arg_confined_addr_of_locals`).
- **contract-panic trio** — (a) the fixtures now carry
  `#![feature(register_tool)] #![register_tool(trust)]` (the tool-attribute
  registration this README diagnosed), and (b) the T9 matcher/used-check
  harvests the static message through the edition-2021 post-inline
  `panic_fmt(fmt::Arguments::from_str("…"))` lowering
  (`generate.rs::panic_call_const_str_messages`, shared by
  `contract_panic_annotation_matches` and `contract_panic_unused_vcs`);
  runtime-formatted messages (`Arguments::new_v1`) remain unmatched,
  fail-closed. The two mutants now refute on their REAL rows (unused
  annotation / unmasked second panic), not vacuously via E0433.

`mutant/extern_write_unbounded_fd.rs` stays quarantined per the analysis
above: refuting a symbolic pointer parameter would re-open the T6
over-refutation class. Root-cause detail for the "Unsupported → Unknown"
verdict, for the record: the native typed-CHC lowering rejects the `usize`
range fact `n <= u64::MAX` (`typed_chc_ay.rs: "integer constant … does not
fit native ay-chc i64"` → InvalidInput → Unsupported on the direct path), and
the proof-grade-only bundle transport (`solve_bundle_native_proof_grade`)
aborts wholesale on the FIRST refuted obligation ("counterexample evidence is
not a proof"), so sibling verdicts degrade to Unsupported as well.

---

Diagnosed 2026-07-06. Sibling green fixtures from the same commit that stay in
the gate: `proved/{method_named_write, std_ffi_safe_paths,
rwlock_registry_read_write, btreemap_string_registry}`,
`mutant/{write_wild_buf, undocumented_unsafe_sig_call, user_ord_btreemap_get}`.

---

# Quarantined by the absent-callee COUNTED-carrier fix (R3 prerequisite P0)

Three `proved/` fixtures moved here when the absent-callee/drop-glue may-panic
rows gained a COUNTED whole-function carrier (R3 prerequisite). Before that fix
these fixtures "proved" only through a fail-open hole: the bridge minted the
`[trust-absent-callee-assumption]` per-site `PanicFreedom` row for their
unmodeled std callees, but the function's only PUBLIC obligation (the default
trust-mc admission) direct-proved under `ObligationBackwardSlice`, the transport
solve never ran, and the row was silently dropped — `pub fn f() -> u32 {
std::process::id() }` compiled CLEAN under the default strict policy (probes
T5d/T6; see `mutant/absent_callee_call_only_mono.rs`). The pre-existing abort
(`transport_rows_have_unproved_assumption_panic`, with its own "model the
call/drop as total, or rewrite it … `-Z trust-policy=advisory` downgrades" error text) is
the in-tree doctrine for exactly this class; the carrier fix re-arms it.

Each fixture's claim is TRUE of std's actual semantics but currently UNPROVEN —
a completeness gap, not a soundness hole. They return to `proved/` when their
callees get audited, type-gated total summaries (the `::BTreeMap::iter` /
`tcx_clone_is_total` precedent):

## `proved/btreemap_string_registry.rs` — needs `BTreeMap::<String, _>::get` totality

`specs.get(key)` dispatches `String: Ord` (total in std, but `get` is
deliberately OUTSIDE the blanket total envelope — the user-`Ord` twin
`mutant/user_ord_btreemap_get.rs` pins why). Re-proving needs a RECEIVER-TYPED
total summary for `BTreeMap::<String, _>::get` (std `String: Ord` is total),
never a blanket `::get`. The T3/T4 regression pins it carried (OpaqueConst
operand typing, `BTreeMap::iter` totality) remain exercised: the fixture now
fails on the `get` absent-callee row only, not on the pinned classes.

## `proved/rwlock_registry_read_write.rs` — needs `RwLock::{read,write}` + `HashMap` totality

`RwLock::read`/`write` return `Result<Guard, PoisonError>` (poison is an `Err`,
not a panic); `HashMap::{new,insert,get}` with `u32` keys run the total SipHash
surface (allocation is OOM-abort, outside the panic model). Both are auditable
total-summary candidates. The T1 pin (POSIX `read(2)`/`write(2)` FFI summaries
must not bind by bare terminal name) still holds — the failure is the
absent-callee row, not an fd-range demand.

## `proved/std_ffi_safe_paths.rs` — needs `OsStr::to_str`/`OsString::push`/`env::vars_os` totality

All three are total std surface (`to_str` is validation returning `Option`;
`push` allocates but runs no user code; `vars_os` cannot panic — unlike `vars`).
The T5A pin (no `::ffi::` namespace SAFETY demands on safe fns) still holds —
the failure is the absent-callee row, not a missing-SAFETY demand.

## pty_fd_seam.rs (proved) — re-quarantined 2026-07-07

The unsafe-lane blockers are FIXED (SAFETY-comment brace-walk scan; confined
&raw-mut call-arg discharge — both landed with green unit pins). The remaining
refusal is the CROSS-LANE gap: the trust-full-verifier bundle lane treats the
extern `dup`/`fcntl` calls as ABSENT CALLEES with unproven panic-freedom
(b63a18b764's fatal class) — the FfiSummaryDb covers only the vcgen FFI lane.
RESTORE WHEN: extern/libc calls with registered FFI summaries are modeled as
panic-free (total) in the bundle/native lane too — the same totality-summary
work the three absent_callee_* fixtures below wait on. Soundness pin retained
meanwhile: mutant/write_wild_buf.rs (active) refutes FFI misuse in the lane
that IS wired.

## `proved/ffi_link_name_getuid.rs` + `mutant/ffi_link_name_getuid.rs` — added 2026-07-07 (T9 link_name alias)

The T9 fix itself is LANDED and unit-pinned (trust-vcgen
`test_libc_getuid_link_name_alias_binds_getuid_contract`): the FfiSummaryDb
registers a narrow `libc_getuid` alias so aterm-types' `#[link_name = "getuid"]
fn libc_getuid()` import binds getuid's Safe/ret>=0 summary instead of failing
closed as "unmodeled FFI call" (extraction drops link_name; the general
link_name-on-`Terminator::Call` fix needs a new serialized field constructed in
~350 places). The PAIR is quarantined for the same reason as `pty_fd_seam.rs`
directly above: a summary-bound extern call still hits the bundle/native lane's
absent-callee panic-freedom row, so no extern-calling fixture can sit in the
green `proved/` lane yet. RESTORE WHEN pty_fd_seam.rs restores (FFI summaries
modeled as panic-free in the bundle lane); the mutant (a renamed, summary-less
import must KEEP failing closed) is expected to hold already.

## float_clamp_bounded_add (2026-07-07) — T5 partial
The vcgen T5 recognizer DOES fire: the aterm-types contrast/luminance float
Add moves FAILED -> runtime-checked at L0 (is_ord_clamp_call + float_exp_bound
clamp-literal interval fact). But the native trust_mc full-verifier lane has
no float theory (status Unsupported), so a strict-lane PROVED fixture can't
pass. RESTORE WHEN: native verifier gains f32/f64 interval/NaN support (out of
scope for the vcgen-level fix). The L0 improvement ships regardless.

## contract_panic_formatted_message (2026-07-07) — T7 matcher wiring
The matcher (fmt_template_literal_pieces decoder + is_arguments_template_new_call
+ template_const_bytes_candidates) is correct and unit-green, and convert.rs
extracts the format_args! byte-array template. But end-to-end the &[u8; N]
template constant still lowers to OpaqueConst, not ConstValue::Str, so the
matcher never sees the bytes and a formatted panic!("... {}", x) stays FAILED
instead of reclassifying. RESTORE WHEN: str_ref_bytes_from_value's ref-peel
loop is fixed to read the &[u8; N] array-ref valtree (isolated repro: this
fixture; the const-message twin contract_panic_annotated.rs proves green).
Zero score impact (aterm-alloc already uses const messages); pure hygiene.

---

## RESTORED 2026-07-24: `mutant/str_slice_computed_byte_offset_oob.rs` — str char-boundary

The one SOUNDNESS fixture in this directory (it pinned a false-accept, not a
capability gap) is back in the gated `mutant/` lane. A `&str` range-slice at a
COMPUTED byte offset whose byte-bounds come from `s.as_bytes()` + a raw
`while i < bytes.len()` loop — an INDEPENDENT bounds credit that never routes
through `char_indices` — was proved CLEAN by the pre-fix binary
(`4 proved, 0 failed`, rc 0) even though `drop_lead("fée")` panics at runtime
("byte index 2 is not a char boundary"). Root cause: `str` is extracted as
`[u8]` (`ty_convert.rs`) and the `Index::index` callee renders generically, so
the RangeIndex bounds VC modeled only the byte-bounds panic, never the UTF-8
char-boundary panic.

The fix is `3f93cbb5bd` ("verify(str): close the str range-slice char-boundary
FALSE-ACCEPT"), unit-pinned by
`crates/trust-vcgen/tests/str_char_boundary_failclose.rs`: `func_operand_name`
appends a `::<__trust_str_index>` marker to a `str` `Index::index` callee (the
Self identity that survives the `str`→`[u8]` erasure), and the RangeIndex body
fails closed for a str receiver unless EVERY explicit endpoint is provably a
char boundary (a `char_indices()` yield / the constant 0). `[u8]`/`[T]` slices
are byte-identical (no marker), and the change is monotone toward refutation, so
it cannot introduce a NEW false-accept.

Verified on a stage-2 `trustc` containing that fix (built at `5c5632c6b`, of
which `3f93cbb5bd` is an ancestor), using the gate's own invocation and verdict
predicates: rc 1, `[slice] FAILED (ay-in-process)` with a counterexample,
`Level 0 summary: 1 failed`, no tool-error pattern — i.e. `refuted`, the exact
char-boundary fail-close this fixture demands, not an incidental unknown.

## `mutant/iterator_product_overflow_silent.rs` (2026-07-10) — sum/product overflow

**A confirmed SILENT false-accept whose fix is a POLICY choice, not yet decided.**
`(1..=n).product::<i32>()` overflows for n >= 13 (debug panic), yet trustc exits 0
with ZERO obligations and ZERO output. The multiply is INTERNAL to `Iterator::
product`, so no caller-visible BinaryOp exists; trust-vcgen `overflow_arith_call`
(generate.rs:15542) DELIBERATELY excludes sum/product to avoid false-failing
`vec.sum()`, and the sound UNKNOWN `PanicFreedom` obligation the trust-ir bridge
mints (`closure_driving_consumer_call`, lower.rs:10570) lives only in the
non-decisive trust-ir SHADOW spine (a Pillar-4 gap).

POLICY DECIDED (owner, 2026-07-10): **runtime-checked demotion**. FIX IMPLEMENTED
in `crates/` — trust-vcgen `iterator_integer_fold_call` mints an `UnsupportedMir
{ kind: "iterator-fold-overflow" }` obligation (→ Unknown → runtime-checked in the
default lane, exactly like the `m[&k]` map-index backstop, verified on a live
binary), unit-pinned by `crates/trust-vcgen/tests/iterator_fold_overflow.rs`. So
this fixture NEVER moves to `mutant/` (runtime-checked demotion is rc 0 by design,
not a refutation). EXPECTED post-rebuild verdict: the obligation is an UNMARKED
`UnsupportedMir` (no `panic-freedom-unverified` marker), so per the current-source
rc doctrine (`report_strict_l0_verification_failure`: non-Failed → "reported, not
errors") it should land runtime-checked at **rc 0** (option C) — but this is
E2E-UNVERIFIED: the only available binary (84e63de6c1) PREDATES that doctrine and
gives **rc 1** for the sibling `m[&k]`/`slice::repeat` runtime-checked cases, so it
cannot predict the rebuilt rc. SOUND EITHER WAY — whether it demotes (rc 0) or
rejects (rc 1), the silent 0-obligation accept is closed and it is never a
false-accept; only the drop-in (Pillar-5) characterization is uncertain until a
rebuild. (A CORRECTION: an earlier note here claimed rc 0 was "verified on the
live binary" — that was a pipe-`$?` misread of grep's exit, not trustc's.) See
memory `project-trust-iterator-sum-product-falseaccept`.
