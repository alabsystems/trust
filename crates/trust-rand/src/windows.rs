// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! The Windows entropy arms.
//!
//! # COMPILE-VERIFIED ONLY. NOTHING IN THIS FILE HAS EVER BEEN EXECUTED.
//!
//! This tree is developed on `aarch64-apple-darwin`. Every function below was
//! type-checked against the real Windows `std` for
//! `x86_64-pc-windows-msvc`, `i686-pc-windows-msvc`, `aarch64-pc-windows-msvc`
//! and `x86_64-win7-windows-msvc`, and **not one of them has been run**. Treat
//! the FFI declarations as reviewed-and-cited, not as measured. The pure logic
//! wrapped around them — return-value classification and the chunk split — is
//! hoisted into [`crate::winret`] precisely so that it *can* be executed here,
//! and it is; see that module's header for what that does and does not buy.
//!
//! # Why this file exists: a Windows capability loss, not a Windows feature
//!
//! `trust-proof-cert` is reachable from the compiler
//! (`compiler/rustc_mir_transform/Cargo.toml` -> `trust-router` ->
//! `trust-proof-cert` -> this crate). Trust is a `rust-lang/rust` fork whose
//! release gate is drop-in compatibility, and the package this crate retires
//! (`rand`, via `getrandom`) built on Windows. A `compile_error!` here would
//! mean *the compiler does not build on Windows*, which is a defect, not a
//! scope decision.
//!
//! # Which entry, and why
//!
//! Three interfaces were considered. All three are reachable with a bare
//! `extern "system"` declaration and **no crate dependency** — `windows-sys`
//! and `libc` are exactly the units this program is removing, and a
//! declaration is not a dependency (the same argument `crate::os` makes for
//! `getentropy`).
//!
//! | Entry | DLL | Returns | Available since | Verdict |
//! |---|---|---|---|---|
//! | `ProcessPrng` | `bcryptprimitives.dll` | `BOOL`, documented as always `TRUE` | Windows 10 v1809 (build 17763) | **PRIMARY** |
//! | `BCryptGenRandom` + `BCRYPT_USE_SYSTEM_PREFERRED_RNG` | `bcrypt.dll` | `NTSTATUS` | Windows Vista / Server 2008 | **FALLBACK** |
//! | `RtlGenRandom` (`SystemFunction036`) | `advapi32.dll` | `BOOLEAN` | Windows XP | legacy; `win7` targets only |
//!
//! **`ProcessPrng` is the primary** for four reasons, in the order they
//! mattered:
//!
//! 1. **It is what `std` itself calls.** `library/std/src/sys/random/windows.rs`
//!    is `c::ProcessPrng(bytes.as_mut_ptr(), bytes.len())` and nothing else, on
//!    every Windows target except `target_vendor = "win7"`. Matching `std`'s
//!    own primitive means Trust's entropy on Windows is exactly as good as the
//!    standard library's, and that the platform floor this crate imposes is one
//!    the compiler already imposes.
//! 2. **Microsoft names it the primary interface.** Its reference page
//!    describes `BCryptGenRandom` as forwarding to the same per-processor
//!    user-mode PRNG, which makes `BCryptGenRandom` a longer path to the same
//!    bytes rather than a better source.
//! 3. **No handle, no algorithm provider, no length ceiling.** `cbData` is
//!    `SIZE_T`, so an arbitrarily large request is one call — no chunk loop, so
//!    no truncation hazard to get wrong. `BCryptGenRandom` takes a `ULONG` and
//!    needs one.
//! 4. **Infallible by contract, and therefore a clean fail-closed signal.** The
//!    documented return value is `TRUE`, full stop. Anything else is a contract
//!    violation with no defined meaning, so it routes straight to the fallback
//!    arm and, failing that, to [`crate::EntropyError`]. It never yields bytes.
//!
//! **`BCryptGenRandom` is the fallback** rather than the primary because it is
//! strictly the longer path (a wrapper over the same PRNG), needs the
//! `BCRYPT_USE_SYSTEM_PREFERRED_RNG` flag to avoid opening an algorithm
//! provider, reports through `NTSTATUS` — which is *not* a Win32 error code and
//! does not set the thread's last-error value, a trap closed in
//! [`crate::winret::ntstatus_is_success`] — and caps a single call at
//! `ULONG` bytes. What it buys is a second, independently-imported code path
//! over the same source, which is precisely the relationship
//! `crate::urandom` has with `crate::os` on Unix: on Linux `getentropy` and
//! `/dev/urandom` are also one kernel CSPRNG behind two access paths. A
//! fallback arm here buys path diversity, not source diversity, and this file
//! does not claim otherwise.
//!
//! **`RtlGenRandom` is rejected for every modern target.** Microsoft documents
//! it under a disclaimer that it may be altered or unavailable in later
//! releases; it is exported under the undocumented name `SystemFunction036` and
//! has to be reached through a `#[link_name]` alias; it is unavailable to
//! AppContainer/UWP processes; and its `ULONG` length needs the same chunk loop
//! `BCryptGenRandom` does. `std` uses it in exactly one place — the
//! `target_vendor = "win7"` targets, where `ProcessPrng` does not exist — and
//! this file makes the same call in the same place, for the same reason.
//!
//! # Minimum supported Windows version
//!
//! **Windows 10, version 1809 (build 17763)**, for the ordinary
//! `*-pc-windows-*`, `*-uwp-windows-*` and `arm64ec-*` targets. That is the
//! minimum-supported-client line on Microsoft's `ProcessPrng` reference and it
//! sits at or below `rustc`'s own floor for those targets (Windows 10), so this
//! crate does not narrow what the compiler already supports.
//!
//! For the tier-3 `*-win7-windows-*` targets the floor is **Windows Vista /
//! Server 2008** — `BCryptGenRandom`'s — with `RtlGenRandom` (Windows XP)
//! behind it. Those targets select the legacy pair below and never reference
//! `ProcessPrng`, exactly as `std` does.
//!
//! # Availability is a LOAD-time question, not a runtime one
//!
//! This is the Windows transposition of `crate::os`'s link-time argument, and
//! it bounds what the fallback arm can rescue.
//!
//! All three declarations use `kind = "raw-dylib"`, which makes the compiler
//! synthesise an ordinary import-table entry from the DLL name — no import
//! library required, which is why `std` uses it for `bcryptprimitives.dll`
//! (*"we can't rely on there being an import library"*,
//! `library/std/src/sys/pal/windows/c.rs:101`). A normal import is resolved by
//! the loader **before `main` runs**: on a Windows too old to export
//! `ProcessPrng`, the process fails to start with a missing-entry-point error.
//!
//! So the `BCryptGenRandom` arm does **not** rescue an old Windows — that case
//! is loud, at process start, and cannot degrade into weak bytes. What the
//! fallback arm covers is the *runtime* failure: `ProcessPrng` present but
//! returning a value other than `TRUE`. That is a narrow window, and naming it
//! precisely is the point; the alternative would be claiming a compatibility
//! range this file does not deliver.
//!
//! On 32-bit x86 the declarations additionally carry
//! `import_name_type = "undecorated"`, because `extern "system"` is `stdcall`
//! there and the import would otherwise be sought under its decorated name
//! (`_ProcessPrng@8`), while the DLLs export the plain symbol. `std` applies
//! the same attribute for the same reason, and the `i686-pc-windows-msvc`
//! compile check below covers it.

/// `ProcessPrng` — the primary arm on every Windows target that has it.
#[cfg(not(target_vendor = "win7"))]
pub(crate) mod process_prng {
    use std::io;

    use crate::winret;

    /// `BOOL`, as `library/std/src/sys/pal/windows/c/windows_sys.rs:205`
    /// declares it: `pub type BOOL = i32;`.
    type BOOL = i32;

    /// Human-readable name of this arm, used in [`crate::EntropyError`]'s
    /// message. It names the DLL as well as the function because "which
    /// `bcryptprimitives.dll` got loaded" is the interesting question when this
    /// arm fails.
    pub(crate) const NAME: &str = "ProcessPrng (bcryptprimitives.dll)";

    // Signature, from Microsoft's `processprng.h`:
    //     BOOL ProcessPrng(PBYTE pbData, SIZE_T cbData);
    // `PBYTE` is `unsigned char *` and `SIZE_T` is `usize` on every Windows
    // target. This mirrors `library/std/src/sys/pal/windows/c.rs:101-110`
    // verbatim, including the x86 `import_name_type`.
    #[cfg_attr(
        target_arch = "x86",
        link(name = "bcryptprimitives", kind = "raw-dylib", import_name_type = "undecorated")
    )]
    #[cfg_attr(not(target_arch = "x86"), link(name = "bcryptprimitives", kind = "raw-dylib"))]
    unsafe extern "system" {
        fn ProcessPrng(pbdata: *mut u8, cbdata: usize) -> BOOL;
    }

    /// Fill `dest` entirely from `ProcessPrng`, or return an error.
    ///
    /// There is no chunk loop because there is no length limit: `cbData` is
    /// `SIZE_T`, so `dest.len()` is always representable and always requested
    /// in full.
    ///
    /// On error the contents of `dest` are unspecified and must not be used.
    pub(crate) fn fill(dest: &mut [u8]) -> io::Result<()> {
        if dest.is_empty() {
            // As in `crate::os`: no reason to cross the FFI boundary for zero
            // bytes, and an empty slice's dangling-but-aligned pointer is never
            // handed to a foreign function.
            return Ok(());
        }

        // SAFETY: `dest.as_mut_ptr()` is valid for writes of `dest.len()` bytes
        // — that is what `&mut [u8]` means — `u8` needs no alignment beyond 1,
        // and `dest.len()` is exactly the count passed as `cbData`. The callee
        // writes at most that many bytes and does not retain the pointer.
        let ret = unsafe { ProcessPrng(dest.as_mut_ptr(), dest.len()) };

        winret::bool_is_true(NAME, ret)
    }
}

/// `BCryptGenRandom` — the fallback arm everywhere, and the primary arm on the
/// `win7` targets, where [`process_prng`] does not exist.
pub(crate) mod bcrypt {
    use core::ffi::c_void;
    use std::io;

    use crate::winret;

    /// `NTSTATUS`, as `library/std/src/sys/pal/windows/c/windows_sys.rs:2988`
    /// declares it: `pub type NTSTATUS = i32;`.
    type NTSTATUS = i32;

    /// Human-readable name of this arm, used in [`crate::EntropyError`]'s
    /// message. The flag is part of the name because the call means something
    /// materially different without it.
    pub(crate) const NAME: &str = "BCryptGenRandom (bcrypt.dll, BCRYPT_USE_SYSTEM_PREFERRED_RNG)";

    /// `BCRYPT_USE_SYSTEM_PREFERRED_RNG`, from `bcrypt.h`:
    /// `#define BCRYPT_USE_SYSTEM_PREFERRED_RNG 0x00000002`.
    ///
    /// With this flag the `hAlgorithm` parameter **must** be `NULL` and the
    /// system-preferred RNG is used directly, which is what removes the
    /// `BCryptOpenAlgorithmProvider` / `BCryptCloseAlgorithmProvider` pair —
    /// and with it a handle to leak and two more calls to check.
    const BCRYPT_USE_SYSTEM_PREFERRED_RNG: u32 = 0x0000_0002;

    /// `cbBuffer` is a `ULONG`, so one call can carry at most `u32::MAX` bytes.
    ///
    /// This is not a tuning parameter and the loop it drives is not decoration:
    /// without it a request larger than 4 GiB would have its length silently
    /// truncated by the `as u32` cast and the tail of the buffer would be left
    /// exactly as the caller supplied it — for a freshly zeroed seed, zeros.
    /// That is the same class of defect `crate::os`'s 256-byte chunking exists
    /// to prevent, and the split itself is tested in
    /// [`crate::winret::fill_in_chunks`]'s tests, which do run on this machine.
    const MAX_PER_CALL: usize = u32::MAX as usize;

    // Signature, from Microsoft's `bcrypt.h`:
    //     NTSTATUS BCryptGenRandom(
    //         BCRYPT_ALG_HANDLE hAlgorithm,   // PVOID
    //         PUCHAR            pbBuffer,
    //         ULONG             cbBuffer,
    //         ULONG             dwFlags);
    //
    // `raw-dylib` rather than a plain `link` so that building for Windows never
    // needs `bcrypt.lib` from the Windows SDK to be on the library path — the
    // same reason `std` gives for `bcryptprimitives.dll`.
    #[cfg_attr(
        target_arch = "x86",
        link(name = "bcrypt", kind = "raw-dylib", import_name_type = "undecorated")
    )]
    #[cfg_attr(not(target_arch = "x86"), link(name = "bcrypt", kind = "raw-dylib"))]
    unsafe extern "system" {
        fn BCryptGenRandom(
            h_algorithm: *mut c_void,
            pb_buffer: *mut u8,
            cb_buffer: u32,
            dw_flags: u32,
        ) -> NTSTATUS;
    }

    /// Fill `dest` entirely from `BCryptGenRandom`, in [`MAX_PER_CALL`]-byte
    /// chunks.
    ///
    /// On error the contents of `dest` are unspecified and must not be used.
    pub(crate) fn fill(dest: &mut [u8]) -> io::Result<()> {
        winret::fill_in_chunks(dest, MAX_PER_CALL, |chunk| {
            // `fill_in_chunks` guarantees `chunk.len() <= MAX_PER_CALL`, which
            // is `u32::MAX`, so this conversion is exact rather than
            // truncating. It is written as a checked conversion anyway, so that
            // raising `MAX_PER_CALL` by mistake becomes an error instead of a
            // silent short request.
            let cb_buffer = u32::try_from(chunk.len()).map_err(|_| {
                io::Error::other(format!(
                    "{NAME}: a {} byte chunk exceeds the ULONG cbBuffer parameter; \
                     the chunk limit and the parameter type have drifted apart",
                    chunk.len()
                ))
            })?;

            // SAFETY: `hAlgorithm` is NULL, which is required (not merely
            // permitted) by BCRYPT_USE_SYSTEM_PREFERRED_RNG.
            // `chunk.as_mut_ptr()` is valid for writes of `chunk.len()` bytes,
            // `u8` needs no alignment beyond 1, and `cb_buffer` is exactly
            // `chunk.len()`. The callee writes at most that many bytes and does
            // not retain the pointer.
            let status = unsafe {
                BCryptGenRandom(
                    core::ptr::null_mut(),
                    chunk.as_mut_ptr(),
                    cb_buffer,
                    BCRYPT_USE_SYSTEM_PREFERRED_RNG,
                )
            };

            winret::ntstatus_is_success(NAME, status)
        })
    }
}

/// `RtlGenRandom` — the fallback arm on the `win7` targets only.
///
/// Present for one reason: on `*-win7-windows-*` the primary arm is
/// [`bcrypt`], and a platform with a single arm would not be fail-closed in the
/// same shape as every other platform this crate supports. `std` makes the same
/// choice of function for the same target family
/// (`library/std/src/sys/random/windows.rs`, `#[cfg(target_vendor = "win7")]`).
#[cfg(target_vendor = "win7")]
pub(crate) mod rtl_gen_random {
    use core::ffi::c_void;
    use std::io;

    use crate::winret;

    /// Human-readable name of this arm, used in [`crate::EntropyError`]'s
    /// message. Both names are given because the export is `SystemFunction036`
    /// and a reader looking at a dependency walker will see that one.
    pub(crate) const NAME: &str = "RtlGenRandom / SystemFunction036 (advapi32.dll)";

    /// `RandomBufferLength` is a `ULONG`; see [`super::bcrypt::MAX_PER_CALL`]
    /// for why the chunk loop is load-bearing rather than decorative.
    const MAX_PER_CALL: usize = u32::MAX as usize;

    // Signature, as Microsoft documents it for `RtlGenRandom`:
    //     BOOLEAN RtlGenRandom(PVOID RandomBuffer, ULONG RandomBufferLength);
    //
    // The DLL exports it as `SystemFunction036`, hence the `link_name`. The
    // return is declared `u8` — `BOOLEAN` is `unsigned char` — rather than as a
    // Rust `bool`, which is what the `windows-sys` binding vendored into `std`
    // uses (`library/std/src/sys/pal/windows/c/windows_sys.rs:93`). A Rust
    // `bool` holding any byte other than 0 or 1 is undefined behaviour, so
    // declaring the raw byte and classifying it in safe code is strictly
    // sounder than trusting the callee's byte to be in range.
    #[cfg_attr(
        target_arch = "x86",
        link(name = "advapi32", kind = "raw-dylib", import_name_type = "undecorated")
    )]
    #[cfg_attr(not(target_arch = "x86"), link(name = "advapi32", kind = "raw-dylib"))]
    unsafe extern "system" {
        #[link_name = "SystemFunction036"]
        fn RtlGenRandom(random_buffer: *mut c_void, random_buffer_length: u32) -> u8;
    }

    /// Fill `dest` entirely from `RtlGenRandom`, in [`MAX_PER_CALL`]-byte
    /// chunks.
    ///
    /// On error the contents of `dest` are unspecified and must not be used.
    pub(crate) fn fill(dest: &mut [u8]) -> io::Result<()> {
        winret::fill_in_chunks(dest, MAX_PER_CALL, |chunk| {
            let length = u32::try_from(chunk.len()).map_err(|_| {
                io::Error::other(format!(
                    "{NAME}: a {} byte chunk exceeds the ULONG RandomBufferLength parameter; \
                     the chunk limit and the parameter type have drifted apart",
                    chunk.len()
                ))
            })?;

            // SAFETY: `chunk.as_mut_ptr()` is valid for writes of
            // `chunk.len()` bytes, `u8` needs no alignment beyond 1, and
            // `length` is exactly `chunk.len()`. The callee writes at most that
            // many bytes and does not retain the pointer.
            let ret = unsafe { RtlGenRandom(chunk.as_mut_ptr().cast::<c_void>(), length) };

            winret::boolean_is_true(NAME, ret)
        })
    }
}

#[cfg(test)]
mod tests {
    //! # These tests do not run on the machine this crate is developed on.
    //!
    //! They are compiled for the Windows targets by
    //! `targo check -p trust-rand --target <windows triple> --all-targets`, and
    //! they run for whoever first runs `cargo test` on a Windows host. Their
    //! job is to be there on that day; nothing in this file has been observed
    //! to pass or to fail.
    //!
    //! The tests that *are* observed to fail under mutation live in
    //! [`crate::winret`], which is compiled under `cfg(test)` on every host.

    /// The liveness assertion, in the shape `crate::urandom`'s equivalent
    /// takes: a real draw from this arm, of a size that spans more than one
    /// internal read, is not left at zero.
    ///
    /// False-failure probability for a working CSPRNG: 2^-4096.
    #[test]
    #[cfg(not(target_vendor = "win7"))]
    fn the_primary_arm_fills_the_whole_buffer() {
        let mut buf = [0u8; 512];
        super::process_prng::fill(&mut buf).expect("ProcessPrng is documented as infallible");
        assert!(buf.iter().any(|&b| b != 0), "512 bytes from ProcessPrng were all zero");
        assert!(buf[..256].iter().any(|&b| b != 0), "the first half was left zero");
        assert!(buf[256..].iter().any(|&b| b != 0), "the second half was left zero");
    }

    #[test]
    fn the_bcrypt_arm_fills_the_whole_buffer() {
        let mut buf = [0u8; 512];
        super::bcrypt::fill(&mut buf).expect("BCryptGenRandom with the system-preferred RNG");
        assert!(buf.iter().any(|&b| b != 0), "512 bytes from BCryptGenRandom were all zero");
        assert!(buf[..256].iter().any(|&b| b != 0), "the first half was left zero");
        assert!(buf[256..].iter().any(|&b| b != 0), "the second half was left zero");
    }

    #[test]
    #[cfg(target_vendor = "win7")]
    fn the_legacy_arm_fills_the_whole_buffer() {
        let mut buf = [0u8; 512];
        super::rtl_gen_random::fill(&mut buf).expect("RtlGenRandom must be available on win7");
        assert!(buf.iter().any(|&b| b != 0), "512 bytes from RtlGenRandom were all zero");
    }

    /// Both arms available on this target must fill a buffer that is not a
    /// multiple of any plausible internal block size, all the way to the end.
    #[test]
    fn a_large_odd_draw_is_filled_to_the_end() {
        let len = 4096 + 37;

        #[cfg(not(target_vendor = "win7"))]
        {
            let mut buf = vec![0u8; len];
            super::process_prng::fill(&mut buf).expect("ProcessPrng");
            assert!(buf[4096..].iter().any(|&b| b != 0), "ProcessPrng left the tail zero");
        }

        let mut buf = vec![0u8; len];
        super::bcrypt::fill(&mut buf).expect("BCryptGenRandom");
        assert!(buf[4096..].iter().any(|&b| b != 0), "BCryptGenRandom left the tail zero");
    }

    #[test]
    fn an_empty_request_is_a_no_op_on_every_arm() {
        #[cfg(not(target_vendor = "win7"))]
        super::process_prng::fill(&mut []).expect("an empty request must succeed");

        super::bcrypt::fill(&mut []).expect("an empty request must succeed");

        #[cfg(target_vendor = "win7")]
        super::rtl_gen_random::fill(&mut []).expect("an empty request must succeed");
    }
}
