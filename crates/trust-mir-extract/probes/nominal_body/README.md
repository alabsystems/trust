# Completed compiler body snapshot custody

This includes the exact new nominal/body modules and runs a real Rustc driver.
It wraps the ORIGINAL mir_for_trust_verification provider, preserving normal
production results except explicit negative-provider corruption cases. While
the real query is in progress it checks that the new reader refuses the missing
completed cache entry without recursively demanding MIR.

The ordinary helper fixture checks the actual immutable elaborated snapshot,
its phase/pass_count, exact signature/argument-local/return types, source
attributes and zero authored contract population, and the existing faithful
extractor's data. It preserves that snapshot after optimized_mir consumes the
original Steal, refuses a stolen body with no retained snapshot, and refuses the
existing provider's actual optimized fallback. Native, legacy and loop clauses
all refuse intact. Negative providers exercise wrong owner, non-Item instance,
promoted source, argument population, selected and UNSELECTED argument types,
return type, missing terminator and local-count budget. These are consistency
controls, not a proof that arbitrary modified query providers preserve semantics.
The optional-result refusal is also checked. There are 36 assertions plus a
nonzero actual in-progress-provider refusal count. constructor_refusal.rs must
fail specifically E0451 for NominalBodyObservation private fields.

Use the maintained Cargo.toml.in in an owned external workspace and the matching
private component recipe described by ../nominal_parameter/README.md. This adds
explicit full-metadata/native pairs for rustc_attr_ir, rustc_index,
trust_mir_extract and trust_types to the observer's compiler externs. No new SDK,
private compiler identity or first-party pin is installed. Actual qualification
used immutable engineering SDKffa141's private driver and matching Trust
seed29ebb with targo --unverified rustc, then affected targo tippy --no-deps.

The runtime driver uses its OWN SDK sysroot, -Zno-codegen,
-Zcodegen-backend=dummy -Zthreads=1 -Ztrust-verify=off, with early GNU jobserver
capture as its FIRST operation. Every build/run goes through build-slot.
The driver explicitly completes trust_mir_mutually_recursive_functions at the
real pre-steal analysis seam BEFORE optimizing fixture bodies. Omitting that
existing producer protocol made a later fallback/SCC read hit a stolen body;
that losing run is not evidence for this new capture reader.

The observed ordinary fixture snapshot is Runtime(PostCleanup), pass_count1,
locals3/blocks4. This is NOT the historical trust-ir-laws TrustVerify-input JSON
and the fixture is not a replay of that whole crate. No provider, parser,
canonical emitter, MIR query name, phase number, output digest or successful
native test establishes original source/body preservation or proof authority.
