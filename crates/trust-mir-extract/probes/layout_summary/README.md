# Closed layout-summary adversaries

`fixture.rs` is ordinary Rust source. `observer.rs` runs against genuine compiler
`TyCtxt` identities and the public layout-safety guards while the selected
function's MIR-building freeze is active. It requests no layout, field offset,
IR lowering or source certificate. The callback continues ordinary compilation
after releasing the freeze, so a malformed source fixture cannot pass through an
early callback stop.

The observer compares the unchanged general callback walk with the specialized
layout walk. Its original 16 named cases check exact generic arguments, recursive unsafe
siblings, a child whose apparent success depends on an outer active ancestor,
opaque/non-leaf-CTFE/generic/escaping-binder refusal, accepted HRTB scope, the
unchanged depth ceiling and completed-summary storage fallback. Two cases carry
associated-type arguments through a depth-six reader: a different generic
instantiation must refuse, and the existing reader depth cap still refuses even
a closed exact argument.

Set `TRUST_LAYOUT_SUMMARY_CANDIDATE=1` only when linking the changed MIR-extract
component. Then only `case_closed_reuse` changes from false to true. The initial candidate
expectation that `case_projection_reuse` would also pass was falsified by an
actual native run; its refusal remains explicit. All other expected results are identical. The observer
asserts the complete population count to reject a vacuous filter.

Build this rustc-private executable using a coherent compiler-private component
closure and its matching compiler seed, then run with that compiler's matching
sysroot. Replacing only metadata or only native artifacts is invalid. The MIR
freeze and queried guard must come from the same selected MIR-extract component.
This is an explicitly unverified native regression; it establishes neither Rust
semantic preservation nor source/proof authority.

## Selected-projection input inventory

The initial 26-case extension includes eight negative projection consumers: a phantom
function pointer, dynamic trait object, opaque argument, non-leaf CTFE constant,
union, opaque impl where-clause, growing generic recursive pointer type, and a
non-generic foreign declaration with an opaque field. The foreign case is a real
separate crate, `foreign.rs`, not an invented compiler type. Build its metadata
with the same compiler used for the observed source compilation, and pass
`--extern layout_summary_foreign=<matching metadata>` to the fixture compilation.
It is not a rustc-private component and does not supply execution/proof authority.

`TRUST_LAYOUT_PROJECTION_CANDIDATE=1` enables the proposed positive expectations
for plain phantom and value-constant carriers and the earlier recursive generic
projection. Leave this unset until linking a complete projection-input candidate.
This separate flag keeps the published closed-layout-only refusal visible.
Numeric work/depth boundaries and malformed compiler-internal constant/type
constructors require owning-helper controls; these ordinary source cases do not
claim to isolate those limits.


The later 41-case population retains those original depth-six cases and adds
separate `ProjectionC` cases at the actual supported reader-depth-five boundary
(argument walk depth six). `TRUST_LAYOUT_SUPPORTED_PROJECTION_CANDIDATE=1`
retains the proposed three positive expectations; the original 26-case and
supported-boundary losing rows remain explicit receipts, including any later
constant-selection refusal. No depth limit is changed to admit a fixture.

The written-RHS pair compares a literal array length with a named leaf constant.
Both direct nominal input guards admit, but an actual unnormalized impl-associated
type query reports a `Value` length for the former and an `AliasConst` length for
the latter. A source-projection ledger may accept the former at the outer
projection; it must refuse the latter rather than substitute the layout reader's
leaf-evaluated answer. `TRUST_LAYOUT_WRITTEN_PROJECTION_CANDIDATE=1` asserts only
the literal written-RHS positive. All mismatch rows are collected, ordinary Rust
analysis completes, and then the process fails if any expectation mismatched.

## Qualified profiles and foreign prerequisites

The complete population is now 47. The exact qualified profile uses
`TRUST_LAYOUT_SUMMARY_CANDIDATE=1`,
`TRUST_LAYOUT_CONFIRMED_PROJECTION_CANDIDATE=1`,
`TRUST_LAYOUT_WRITTEN_PROJECTION_CANDIDATE=1`, and
`TRUST_LAYOUT_FOREIGN_PREPARATION_CANDIDATE=1`.
The confirmed flag selects only the demonstrated recursive and plain-phantom
positives. It does not silently enable the earlier constant-selection expectation.
The old `TRUST_LAYOUT_PROJECTION_CANDIDATE` and
`TRUST_LAYOUT_SUPPORTED_PROJECTION_CANDIDATE` modes remain diagnostic losing
profiles; leave them unset for the qualified profile.

The six additional consumers exercise actual foreign primitive Copy-supertrait
storage, opaque and nonprimitive-supertrait refusals, `NonNull<u8>` acceptance,
and Range/Or pattern refusal. The source compiler accepts the signed Or pattern
`i8 is ..=-1 | 1..` through `std::pat::pattern_type!`. Initial singleton,
unsigned and interior-only Or attempts were compiler-rejected and are not counted
as valid negative consumers. The fixtures execute no pointer operation and claim
no value, dereference, provenance, ABI offset or provider authority.

The maintained observer also creates a fresh `LayoutQuerySafetyContext` inside
each case's actual freeze and checks its result against the same expected guard
result. No context or primed facts pass between cases. This observer requires the
current public MIR-extractor API (published in Trust `f9c345f6`); the earlier frozen
SDK-only baseline logs remain historical controls, not evidence that the older
SDK exports this new API.

## Freeze-frame ownership regression

`frame_owner.rs` observes the real `frame_owner_fixture.rs` TyCtxt owner and
named-leaf array type. It primes one context while an ordinary function frame
is live, enters an unnamed refusing frame, then explicitly drops the outer
guard first. The still-live unnamed guard must continue to forbid CTFE and
the same context must continue to decline the array; after both guards retire
the context reproves it. All four context decisions and the actual callback
population are asserted before ordinary Rust analysis completes. This is a
freeze-policy ownership/epoch regression, not layout, IR/source correspondence,
ABI, proof-grade or compiler qualification. Use the same coherent current
MirExtract component and matching driver/private closure as the other probes.

## Concrete const typing audit profile

`TRUST_LAYOUT_CONCRETE_CONST_CANDIDATE=1` changes only the expected summary and
fresh-context result for `case_supported_const`, whose original written input is
`ConstKind::Value(7_usize)`. It retains the baseline result and all 46 other
expectations. Without this flag, the historical refusal expectation remains.
The unchanged 47-case profile first failed with exactly this one newly admitted
row after the concrete-const proof-tree audit repair; the explicit profile then
passed all 47 cases. The older deep-reader and named-leaf RHS refusals remain.
These native query controls establish no source proof, ABI or machine-code grade.
