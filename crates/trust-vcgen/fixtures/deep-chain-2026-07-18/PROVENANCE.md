# deep-chain fixtures (2026-07-18)

> The dump flags were spelled `-Ztrust-dump-mir` / `-Ztrust-dump-only` when
> these bytes were produced; they are one `-Ztrust-dump=<what>:<dir>` option now.
> The recipe below is the current spelling, so it reproduces against today's
> compiler rather than the pinned one.

Byte-for-byte `-Ztrust-dump=mir:<dir>` dumps of the deep-chain probe (trustc
@c273d6bcf8) — the final 22 a3d-geom residual classes:
* `forward_dot = at.sub(eye).normalized().dot(at)` — the look_at class: the
  dot-callsite actual is `normalized()`'s dest, whose field trace must pass
  THROUGH normalized's guarded division (divisor floor 1e-20).
* `half_point` — the transform_point class: guarded division (`w.abs() >
  1e-20`) with a param-field numerator.
Summary params (probe build): sub=[self,o], normalized=[self], dot=[self,o],
new=[x,y,z] or raw locals.
