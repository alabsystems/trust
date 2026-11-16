# Actual b8 O0 frame input

`actual-b8-caller-input.json` is the complete observed Compiler CER input
produced from the unchanged source-memory-caller subject by the immutable
b8f24f1b5b575f19686a67cda63ff1bb0025459e engineering compiler. Its own strict
compile refused the framed caller. The 639-byte object inside this capture
is byte-identical to the earlier retained b8 caller object. No frame or
source-refinement authority is imported from this diagnostic.

Capture SHA256: fccc4c260617ebf86cc83a8bf32e56a17957aeb48949ea17050a997f116a2dae
Object SHA256: c4b9e1fcbc611f998c791cacd906ae735a5371528725829739995fe92c24e941

The source callee reads a byte before writing one. The caller's actual
STP/MOV/BL/LDP/RET frame is 16 bytes and has no source Alloca. P retains three
64-bit argument locations and the 64-bit result. The complete dump binds both
producer modules, source bodies, M_cg, P, configuration and actual object.
The test neither fabricates an entry heap nor changes the original goal.

The native-instruction concrete controls are counterexamples only: raw
output-pointer aliases can overwrite saved FP/LR, and a separated output still
leaves changed stack bytes at an unrestricted memory query.
