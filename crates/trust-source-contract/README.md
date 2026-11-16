# Shared source contracts

This is the compiler-independent source/contract adapter formerly owned by
`trust-mir-extract::verifier_api`. The extractor re-exports this implementation;
there is one decoder and one set of source, typed-predicate and body-VC identities.

`exact_boolean_ensures_body_group` checks the generated body group for a
bounded Boolean source contract with typed scalar or nominal inputs. It grants no proof authority. It
requires the original typed compiler query, exact postconditions and a unique
bijection with regenerated raw or interval-augmented VCs. Callee-summary-dependent
rows do not pass without their derivations; source IDs alone cannot establish
that relation.

`exact_unsigned_select_ensures_body_group` covers the bounded same-width unsigned
scalar select fragment. It uses the shared ordered-select recognizer, accepts
only bare-value comparisons and exact parameter type-range premises, and checks
all clauses against the complete original generated body-VC carrier. It rejects
extra assumptions, arithmetic, width/domain drift and partial groups. Returned
indices still require checked body-VC certificates and authenticated source
identity before publication. The retained clamp fixtures test correspondence;
their reconstructed query sidecars do not grant either authority.

`exact_ensures_body_group` is the shared dispatcher used by checked source-clause
replay. Boolean and fixed-width unsigned results share the existing typed call
model. Unsigned call bodies pass the same bounded scalar evaluator as inferred
return candidates, with exact argument type-range premises; every authored
clause and every original generated row must match. The entry-domain builder
uses the canonical integer bounds in `trust-semantics`. No additional decoder
or call semantics is introduced.

Candidate callees alone are not proofs. Source replay must independently check
the complete original callee proof graph and the selected original caller body
proofs. Missing identities, type mismatches, additional assumptions and partial
clause groups refuse. The retained width-helper fixtures exercise real compiler
bodies with reconstructed query sidecars; they do not authorize publication or
change the measured self-use Unknown count.
