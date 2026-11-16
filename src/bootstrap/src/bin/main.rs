//! The `main.rs` for bootstrap is a small stub that delegates to the real
//! entry point within the bootstrap library crate.
//!
//! Don't add more code here! Add it to the inner main instead.

#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
#[repr(C, align(8))]
struct FixedBootstrapDeclaration([u8; 64]);
#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
#[used]
#[unsafe(link_section = "__TEXT,__trust_btfix")]
static FIXED_BOOTSTRAP_DECLARATION: FixedBootstrapDeclaration =
    FixedBootstrapDeclaration(build_helper::bootstrap_protocol::BOOTSTRAP_FIXED_PROTOCOL_MARKER);

fn main() {
    // SAFETY: original native entry, before file creation or threads. This
    // syscall-only setup leaves GNU capture as the first descriptor operation.
    unsafe { bootstrap::native_entry::clamp_creation_mask_at_entry() };
    #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
    std::hint::black_box(&FIXED_BOOTSTRAP_DECLARATION);
    #[cfg(any(target_os = "macos", target_os = "linux"))]
    let original_fixed = bootstrap::snapshot_fixed_at_entry().unwrap_or_else(|error| {
        eprintln!("bootstrap: original fixed snapshot refused: {error}");
        std::process::exit(75);
    });
    // Trust: FIRST descriptor operation; never import advertised numbers later.
    // The actual compiler keeps its SDK-first snapshot/GNU import/SDK capture
    // ordering unchanged.
    if let Err(error) = unsafe { bootstrap::capture_scheduler_at_entry() } {
        eprintln!("bootstrap: inherited scheduler capture refused: {error}");
        std::process::exit(75);
    }
    #[cfg(any(target_os = "macos", target_os = "linux"))]
    if let Err(error) = bootstrap::capture_fixed_at_entry(original_fixed) {
        eprintln!("bootstrap: original fixed capture refused: {error}");
        std::process::exit(75);
    }

    bootstrap::cli_main::main();
}
