# Binary-decompile fixtures

The five `*-inprocess-*-elf.hex` objects are runtime inputs for `binary_to_trust_ir_e2e`. Tests need no assembler; missing, corrupt or unwritable inputs fail the tests. Raw object digests are pinned in the Rust consumer.

Explicit regeneration: `python3 tests/fixtures/binary_decomp/regenerate_inprocess_elf.py [--check] [--cc clang]`. Generation validates ELF type, architecture, exact instructions and the single global function symbol before writing. `--check` compares without modifying checked-in files and returns nonzero on drift. Compiler absence fails; it is never a successful skip. A different assembler version can change object layout, so inspect every change and deliberately review Rust digest updates.

Controls: `python3 -B scripts/tests/binary_decomp_inprocess_fixture_test.py -v`. See [native qualification](../../../docs/validation/2026-11-06-binary-fixtures-without-assembler.md). Existing executable and CLI fixtures remain governed by their own scripts and consumers.
