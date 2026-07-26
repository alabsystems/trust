# GitHub Actions

The job must install or select a complete Trust toolchain before this step; the
stock Clippy bundled on hosted runners is not Tippy.

```yml
on: push
name: Tippy check

# Make sure CI fails on all warnings, including Tippy's Clippy-compatible lints
env:
  RUSTFLAGS: "-Dwarnings"

jobs:
  clippy_check:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v7
      # Install/select the project-pinned Trust toolchain here.
      - name: Run Tippy
        run: targo tippy --all-targets --all-features
```
