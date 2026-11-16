# ASL1 CC1 foundation: closed arithmetic leaf

This increment ports the pinned BSD ASLRef ADD/SUB literal branches and their
concrete width/unconstrained-integer typing rules to Lean source for full Clean
reference-entry checking. It starts the missing CC1 language machinery; it is
not the CC1 acceptance result and supplies no physical AArch64 proof authority.

Reference: herd/herdtools7 `ASLRefEAC1`, immutable commit
`ffad2692c4580538e8db7bf6631aa886edfc7423`. `reference/SOURCE.json` binds the
retained complete BSD source files and `reference/aslref/LICENSE.txt` retains
the notice. Operations.ml's `binop_values`, Typing.ml's `apply_binop_types`,
Native.ml's `binop` delegation and Interpreter.ml's `EvalELit`/`EvalBinop` are
the source connection. `BitVec.ofInt` represents Bitvector.of_z's low-bit
extraction, including negative values and width zero. This translation and the
OCaml representation bridge remain a reviewed source seam, not a proved
refinement of OCaml/Zarith/Bitvector's implementation.

`Asl1/Arithmetic.lean` implements the ADD/SUB branches for integer/integer,
equal-width bitvector/bitvector and bitvector/integer. Boolean literals retain
their type and refuse arithmetic. Operand order matters: integer/bitvector
refuses. Theorems prove result-type preservation, constructive typed progress,
modular unsigned readout and exact no-wrap readout under explicit mathematical
bounds. None assumes a successful execution as a replacement for evaluation.

`Asl1/Import.lean` is a structural mirror of AST.mli's relevant constructors,
including all 26 actual binary-operator variant identities.
Every node retains and checks V1; noncanonical bitvector magnitudes, unsupported
operators, expression constructors and literal constructors refuse. Its export /
import theorem preserves the entire supported expression. It is not an ASL text
parser or an extractor from actual OCaml AST values. No proprietary Arm package
has been fetched or ingested by this increment.

The denominator is deliberately explicit: 2 of AST.mli's 26 binary operator
tags; 3 of 6 literal constructors; 2 expression constructors; the concrete
bit-width and unconstrained-integer cases of typing. Real/string/label values,
variables, named/constrained/parameterized types, calls, assignments, slicing,
conditionals, choice, effects and all other language forms remain outside this
leaf. ASLRef's complete tests, licensed package ingestion, normalized two-host
replay, generated machine state/decode/encode/execute/step and emitter census
remain open CC1 requirements. There is no generated Arm machine model yet.

The selected CG `c743bdd425407865772d33c2121112404fa2282d` A64.Machine uses
hand-transcribed flat, wrapping total memory and explicitly excludes mapping,
alignment, faults and other observers. The FORM scalar memory proofs exclude
the same physical preconditions. Neither is promoted or extended here. The
physical frame goal still needs the generated model, mapped/aligned legal
private stack operations, no-wrap address bounds, whole outside-frame world
preservation, raw SP/X29/X30/callee-save restoration and a real return event.
No frontend, codec, ABI, SourceNoUB, body-license or compiler-completion claim is
made, and no selector, grade, policy or compiler admission path changes.

The frozen proven-core plan reports no K2 report and requires its decision for
CC1; no justified K2 no-go was found. KR1 has concrete reference-entry slices
in selected Clean, but that is not a blanket completion claim. The signed
provenance dossier records the terms acceptance (the owner, 2026-10-15:
docs/OWNER_RULINGS.md OW-40); any future
licensed fetch must still require the explicit named terms-acceptance flag and
pinned SHA. This BSD-only increment does not use that acceptance to bypass an
ingestion boundary.


## Actual pinned ASLRef source ingestion

`build_exporter.py` fetches exactly 64 immutable `asllib` files through Agh,
checks Git blob / SHA-256 / size against `ASLREF-PIN.json`, and builds a fresh
external executable with explicitly selected host OCaml packages. It fetches no
Arm machine package and installs nothing. The selected ASLRef notices (including
the upstream `diet` exceptions) stay in the fetched source. The full upstream
parser, strict `Typing.TypeCheckDefault` and `StaticInterpreter` execute; no local
ASL text parser or substitute reference evaluator is supplied.

The local `aslref_export.ml` extension requires exactly one complete function
with no parameters, arguments, override, builtin body or recursion limit; its
complete body must be one value-return statement, before and after typing.
Allowed qualifiers are absent/Pure. Concrete return carriers are unconstrained
integer, bits(0..64), and boolean. The typed return expression is the closed
ADD/SUB leaf, with literal magnitudes bounded by the 64-bit wire representation.
Names and signedness are preserved. Unsupported declarations, body forms,
operators, types, bitfields and bounds refuse rather than selecting a sub-body.
The real typechecker removes the parser's singleton E_Tuple parenthesis markers;
the extractor uses that actual returned AST, with source and typed signatures
checked. It does not implement another source normalizer. Source positions and
allowed qualifier spelling are not serialized.

The packet contains the pinned format identifier, both original/typed names,
return carrier and typed expression. `Asl1/Wire.lean` checks all bytes, complete
consumption, depth/width/canonical-literal constraints, and caller-selected names
and expected return type. Its unconditional `checked_progress` derives actual
leaf evaluation from accepted static typing. The diagnostic reference result is
computed by ASLRef's real Interpreter.Make/StaticBackend through StaticInterpreter;
it is never packet data and never selects a proof goal or expected value.
`WireFixtures.lean` binds six actual producer packets to exact byte lists and
closed results. Controls include malformed/trailing/truncated packets, wrong pin,
wrong caller name/type, unknown operator, inconsistent width and noncanonical
bits, plus closed wrong-result/name/type/operator goals for independent Clean.

Build from fresh external paths (Python 3.11+ and Agh required):

```sh
python3 scripts/trust_core/asl1/build_exporter.py \
  --source-dir /external/new-aslref-source \
  --build-dir /external/new-aslref-build.noindex \
  --tool-bin /owned-host-tools/bin --library-dir /owned-host-tools/lib
python3 scripts/trust_core/asl1/producer_controls.py \
  --producer /external/new-aslref-build.noindex/default/bridge/exporter.exe \
  --out /external/new-source-controls
```

The helper uses build-slot admission. The measured host-tool combination is
OCaml 4.14.2, Dune 3.17.2, Menhir 20231231, Zarith 1.14 and GMP 6.3.0, built from
public source into an owned external prefix. They are producer TCB inputs, not
kernel-verified tools or an installed toolchain update. Native controls run six
source positives, two actual ASL type errors, one parser error and four explicit
profile refusals, with exact phase/kind checks. A second fresh source/build path
produces identical six packet bytes on the same host; this is not CC1's two-host
normalization result or its full ASLRef test denominator.

The pin field identifies a format/source revision; it does not authenticate an
arbitrary incoming packet. Source parsing, typing, normalization, OCaml/Zarith /
Bitvector execution, extraction and source association remain a reviewed TCB
seam. Clean checks the byte-decoded arithmetic mathematics, not a proof of these
producer implementations or whole ASL function/call semantics. No proprietary
Arm data, generated ISA, physical frame/ABI, source refinement, SourceNoUB,
body-license, release, compiler policy or proof-grade authority is added.
