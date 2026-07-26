# GitLab CI

Use a runner image containing the project-pinned Trust toolchain. A stock Rust
image does not contain Tippy.

```yml
# Make sure CI fails on all warnings, including Tippy lints
variables:
  RUSTFLAGS: "-Dwarnings"

tippy_check:
  # image: your-project/trust-toolchain:<pinned-version>
  script:
    - targo tippy --all-targets --all-features
```
