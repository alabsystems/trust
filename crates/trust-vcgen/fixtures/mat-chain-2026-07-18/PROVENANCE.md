# mat-chain fixtures (2026-07-18)

> The dump flags were spelled `-Ztrust-dump-mir` / `-Ztrust-dump-only` when
> these bytes were produced; they are one `-Ztrust-dump=<what>:<dir>` option now.
> The recipe below is the current spelling, so it reproduces against today's
> compiler rather than the pinned one.

Byte-for-byte `-Ztrust-dump=mir:<dir>` dumps of the Mat4 residual-class probe
(`mul_row = self.row(0).dot(v)`; `row(r)` = 4-arm match of `Vec4::new` over
CONSTANT projections) from trustc @a4c75d95b6 — the minimal reproduction of
the remaining 41 a3d-geom unknowns (Vec4::dot-chain preconditions in
mul_mat4/transform_*/look_at): the dot-callsite actual is `row(0)`'s call
dest, whose field trace needs the multi-arm hull over row's four call-dest
defs through the transitive `Vec4::new` passthrough. Summary params (probe
build): row=[self,r], dot=[self,o], new=[x,y,z,w] or raw locals.
