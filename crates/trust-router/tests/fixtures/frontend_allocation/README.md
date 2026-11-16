# Native frontend allocation obligations

These three violation formulas are the exact `Formula` debug ASTs emitted by
Trust for the bounded Prober diagnostic input during the 2026-09-15 frontend
replay. The JSON files encode those same ASTs for the production deserializer;
the regression asserts byte-for-byte Debug equality before executing the native
backend. The origin file hashes both representations and the captured log.

The 1,024-variable bound makes each allocation violation unsatisfiable. Replacing
only the integer bound 1,024 with 268,435,456 admits an allocation-limit violation
and must return a counterexample. The tests preserve the nested conjunctions,
implication guards, saturated multiplication, variable spelling and u64 maximum.
They test router/embedded-solver integration, not complete compiler transport,
heap provenance, vector growth correctness or whole-program verification.
