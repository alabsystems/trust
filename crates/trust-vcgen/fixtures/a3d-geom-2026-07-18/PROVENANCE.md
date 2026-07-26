# a3d-geom whole-crate fixtures (2026-07-18)

> The dump flags were spelled `-Ztrust-dump-mir` / `-Ztrust-dump-only` when
> these bytes were produced; they are one `-Ztrust-dump=<what>:<dir>` option now.
> The recipe below is the current spelling, so it reproduces against today's
> compiler rather than the pinned one.

Byte-for-byte `-Ztrust-dump=mir:<dir>` dumps of EVERY a3d-geom function (trustc
@c273d6bcf8, --cfg feature="contracts") — the ground truth for the final 22
unknowns' in-crate diagnosis. Keyed by each dump's `def_path`, which equals the
call-string callers use (`Vec3::dot` vs `Vec4::dot`).
