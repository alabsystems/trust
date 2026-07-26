# `src/ci`

Only `channel` lives here. It is not CI configuration: it is the release
channel identity of the checkout, and it is read at build, tidy, publish, and
release-gate time.

The path is load-bearing rather than merely conventional — it is spelled as a
literal string in bootstrap's config resolution, tidy's feature-gate staleness
check, `bump-stage0`, targo's build-commit stamping, the reference's
`mdbook-spec` preprocessor, and the `targo trust` release identity/prepublish
gates, several of which resolve it out of a *source tarball* or a *historical
commit* rather than the working tree. Renaming or moving it is therefore a
coordinated change across all of those readers, not a file move.

A Trust release requires this file to read exactly `trust`; publishing under a
stock Rust channel name is refused by `targo trust prepublish`.
