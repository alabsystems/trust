# center-chain fixtures (2026-07-18)

> The dump flags were spelled `-Ztrust-dump-mir` / `-Ztrust-dump-only` when
> these bytes were produced; they are one `-Ztrust-dump=<what>:<dir>` option now.
> The recipe below is the current spelling, so it reproduces against today's
> compiler rather than the pinned one.

Byte-for-byte `-Ztrust-dump=mir:<dir>` dumps of the `Aabb::center` chain probe
(`center = self.min.add(self.max).scale(0.5)`, contracts ON) from trustc
@c072b2e781 — the minimal reproduction of the a3d-geom struct-chain
precondition residual: the `Vec3::add` callsite F5-suppresses but the
`Vec3::scale` callsite (call-dest actual) F5-misses in PRODUCTION while the
hand-built unit replica suppresses. These pin the real compiler-fed inputs.
Summary params (from callee_param_names in the same build): add=[self,o],
scale=[self,s], new=[_1,_2,_3].
