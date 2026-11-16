# Original law entry captures

These eleven JSON files are unchanged compiler dumps of the five requested IR law helpers, their actual external `Linkage::is_module_local` method, and one authored law per helper family. `capture.json` records source/compiler hashes, the original IR commit, exact diagnostic argv and per-file hashes.

The immutable engineering SDK is Trust `ffa141252dceb40e74d991218b336ce0f3516e6d`, built with external LLVM23.1.5. The supported native diagnostic pattern (`-Ztrust-policy=advisory -Ztrust-dump=mir-only:...`, with `TRUST_DUMP_MONO=1`) retains the external inline method through the real codegen inventory. All 411 root obligations were reported unknown/skipped; extraction success earns no proof credit. An earlier explicitly unverified Cargo dump correctly refused the batteries-on requirement; that refusal was retained. There was no model/source rewrite or verifier-gate substitution.

The entry tests use original typed bodies and source clauses. Authored-clause query sidecars are explicitly constructed test inputs, not captured compiler queries. Inferred call inputs are candidates, not independently certified DAGs. These controls establish structural correspondence/refusals only; they do not qualify the five source laws, the full IR gate, a new SDK or source-level `Certified` authority.
