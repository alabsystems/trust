The `retained-clamp-{width,to-max}.json` fixtures preserve the original typed
function JSON and all four generated postcondition VC JSON strings from
`NOV3-TRUST-ON-TRUST-HELPERS/after/trust-intbound`, measured at
`c133258d3c76e6dbff9237cb172e51f3b5c398c9`. Each embedded string keeps its original
SHA-256; the tests check those hashes before decoding with the existing shared
serde types. The two authored-clause accounting markers are excluded from the
body-VC array: they are `false` placeholders, not generated body obligations.

The original exporter did not retain a compiler-query sidecar or authenticated
macro source identity. The tests reconstruct a **query-shaped fixture** using
the existing source parser and exact declared variable domains. This establishes
body-VC correspondence for those inputs, without claiming a retained original
compiler query, live source authority, or a newly checked proof certificate.

Both functions are unsigned fixed-width selects. The shared ordered-select
reader normalizes `a > b` to `a <= b` with the arms exchanged (and `>=` to `<`
likewise). The correspondence accepts only bare scalar comparisons, exact full
parameter type ranges, and the complete original generated body group for every
clause. Additional assumptions, arithmetic/overflow, changed clauses/bodies,
wrong domains, missing rows and duplicated rows remain refused.
