//! `launch` — Trust-vs-Rust launch readiness, HOST-ARCH native subset.
//!
//! The full `launch` rubric (`default_launch_dimensions` /`launch_dimension` in
//! `rust_vs_trust.rs`) spans two architectures — aarch64 and x86-64 — across
//! compatibility, compile-time, runtime, binary-size, and proof dimensions.
//! A dev checkout can only *natively run* code for the machine it is on. This
//! gate therefore verifies the launch-critical properties that ARE checkable
//! natively on the host triple, and it refuses to claim the cross-arch coverage
//! it cannot execute (per `docs/testing-strategy.md`: fake / manual / stub
//! evidence must never be promoted into a passing dimension).
//!
//! The host-arch launch-critical properties proven here, each of which can
//! genuinely fail:
//!
//! 1. The toolchain reports the host triple via `trustc -vV`, and that triple's
//!    architecture agrees with the effective architecture of the running
//!    `targo-trust` process (`std::env::consts::ARCH`). This deliberately does
//!    not claim to identify physical hardware through an emulation layer.
//! 2. `trustc` compiles AND links a runnable executable from a trivially-safe
//!    fixture under its default, verify-by-default settings — a daily-driver
//!    toolchain must not spuriously refuse safe host code, and must actually
//!    emit a linked binary.
//! 3. The emitted object file's header (ELF / Mach-O / PE) encodes that same
//!    effective process architecture, so successful execution alone cannot
//!    launder an object built for a different process architecture into a pass.
//! 4. The binary runs successfully on this machine.
//! 5. The public `targo trust` CLI and root-resolution transport gates pass;
//!    direct-compiler success alone is not enough launch evidence.
//!
//! Scope is stated explicitly in the transcript: this run stands in for the
//! host launch arch only. The non-host launch arch (and its compat / perf /
//! size dimensions) requires a native runner on that architecture and is
//! deliberately NOT asserted here.

use std::env;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

use anyhow::{Context, Result, bail};

use super::trustc_native::{self, Captured, capture};
use super::{
    GatePolicy, find_stage2_tool, read_bounded_exact_file_under, scrub_gate_process_environment,
    section,
};

const LAUNCH_FIXTURE_SOURCE: &str = "pub fn launch_safe_midpoint(a: usize, b: usize) -> usize {\n    (a / 2) + (b / 2)\n}\n\nfn main() {\n    let _ = launch_safe_midpoint(4, 6);\n}\n";
const LAUNCH_VERIFICATION_SESSION: &str = "trust-added-launch";

/// Generous upper bound for a statically-std-linked hello-world executable.
const MAX_LAUNCH_BINARY_BYTES: u64 = 256 * 1024 * 1024;

pub(crate) fn run(root: &Path, policy: GatePolicy) -> Result<()> {
    section("Trust-vs-Rust launch readiness (host-arch native subset)");

    let (native_arch, cross_arch) = native_launch_arch()?;
    println!(
        "Policy: strict={}, release={} (every host-arch step below already fails closed).",
        policy.strict, policy.release
    );
    println!("Effective architecture of the running targo-trust process: {native_arch}");
    println!(
        "Arch scope: this native host check covers the `{native_arch}` launch arch ONLY. The \
         cross-arch (`{cross_arch}`) launch dimensions require a native runner on that \
         architecture and are deliberately NOT claimed here (no fake cross-arch pass)."
    );

    let scratch = tempfile::Builder::new()
        .prefix("trust_launch_host_")
        .tempdir()
        .context("failed to create launch scratch dir")?;
    let scratch = scratch.path();

    let trustc = locate_trustc(root)?;
    println!("Using stage2 trustc: {}", trustc.display());
    println!();

    // Launch readiness includes the user-facing driver and its config/cache
    // root binding. A direct trustc-only probe cannot stand in for those paths.
    println!("--- public CLI and root-resolution transport");
    trustc_native::public_cli(root, policy)?;
    trustc_native::root_resolution(root, policy)?;
    println!("  PASS: public CLI and root-resolution transport passed");
    println!();

    // 1. The toolchain names the host it runs on, and it agrees with this
    // process's effective architecture.
    println!("--- host triple identity (trustc -vV)");
    let triple = toolchain_host_triple(&trustc, scratch)?;
    let reported_arch = triple_arch(&triple);
    println!("trustc -vV host triple: {triple}");
    if reported_arch != native_arch {
        bail!(
            "trustc -vV reports host triple `{triple}` (arch `{reported_arch}`), but the running targo-trust process is `{native_arch}`; the toolchain misidentifies its effective host"
        );
    }
    println!("  PASS: toolchain host triple matches the effective process arch ({native_arch})");
    println!();

    // 2. trustc compiles AND links a runnable host executable, verify-by-default.
    println!("--- compile + link a host executable (default verify-by-default settings)");
    let source = scratch.join("launch_host_fixture.rs");
    fs::write(&source, LAUNCH_FIXTURE_SOURCE).context("failed to write launch fixture source")?;
    let binary_name = if cfg!(windows) { "launch_host_fixture.exe" } else { "launch_host_fixture" };
    let binary = scratch.join(binary_name);

    let mut compile = trustc_command(&trustc, scratch)?;
    compile
        .args([
            "-Z",
            "trust-verify-output=json",
            "-Z",
            &format!("trust-verify-session={LAUNCH_VERIFICATION_SESSION}"),
        ])
        .args(["--edition", "2021", "--crate-name", "launch_host_fixture"])
        .arg("-o")
        .arg(&binary)
        .arg(&source);
    let compiled = capture(compile)?;
    if !compiled.exited_with(0) {
        bail!(
            "trustc failed to compile+link the launch fixture (exit {}); a daily-driver toolchain must compile trivially-safe host code without refusal\nstdout:\n{}\nstderr:\n{}",
            compiled.exit,
            compiled.stdout,
            compiled.stderr
        );
    }
    let Some(outcomes) =
        trustc_native::authenticated_outcomes(&compiled, LAUNCH_VERIFICATION_SESSION)
    else {
        bail!(
            "trustc compile succeeded without a complete typed verification transcript bound to session {LAUNCH_VERIFICATION_SESSION}; launch evidence must prove verification remained enabled\nstdout:\n{}\nstderr:\n{}",
            compiled.stdout,
            compiled.stderr
        );
    };
    // Every row must be proved. A `no_obligations` row is the coverage marker
    // for a function with nothing to prove (the fixture's `main`) — it carries
    // no obligation id/location BY NATURE and is not a proof claim, so it must
    // not fail the stable-identity requirement. At least one REAL obligation
    // row (id + location) must still prove, or the run was vacuous.
    let real_proved_rows =
        outcomes.iter().filter(|row| row.kind != "no_obligations").collect::<Vec<_>>();
    if real_proved_rows.is_empty()
        || outcomes.iter().any(|row| !row.outcome.is_proved())
        || real_proved_rows.iter().any(|row| !row.has_obligation_id || !row.has_location)
    {
        bail!(
            "launch fixture verification was vacuous, non-proof, or lacked stable obligation IDs/source locations: {outcomes:?}"
        );
    }
    if !is_executable_file(&binary) {
        bail!(
            "trustc reported success but did not emit a runnable host executable at {}",
            binary.display()
        );
    }
    println!(
        "  PASS: trustc compiled + linked a host executable with complete authenticated verification coverage"
    );
    println!();

    // 3. The emitted object matches the process architecture, rather than a
    //    different process architecture that execution might conceal.
    println!("--- emitted object matches effective process arch `{native_arch}`");
    let binary_bytes =
        read_bounded_exact_file_under(scratch, Path::new(binary_name), MAX_LAUNCH_BINARY_BYTES)
            .context("failed to read the emitted launch executable")?;
    if !binary_arch_matches(&binary_bytes, native_arch)
        .context("could not classify the emitted executable's object format")?
    {
        bail!(
            "the emitted executable's object header does not encode effective process arch `{native_arch}`; trustc did not target the running process architecture"
        );
    }
    println!("  PASS: emitted executable object header encodes `{native_arch}` machine code");
    println!();

    // 4. It actually runs on this machine.
    println!("--- run the host executable");
    let executed = run_host_binary(&binary, &trustc, scratch)?;
    if !executed.exited_with(0) {
        bail!(
            "launch fixture binary exited with status {} instead of 0\nstdout:\n{}\nstderr:\n{}",
            executed.exit,
            executed.stdout,
            executed.stderr
        );
    }
    println!("  PASS: host executable ran successfully");

    println!();
    println!(
        "=== launch (effective process arch `{native_arch}`) native readiness: PASS — public CLI/root transport passed, trustc emitted complete authenticated verification coverage, compiled + linked a matching-arch executable, and that binary ran successfully. Cross-arch `{cross_arch}` launch dimensions remain out of scope for this native host check. ==="
    );
    Ok(())
}

/// Map the target architecture of the running `targo-trust` process onto the
/// launch rubric's arch tokens, returning `(host_launch_arch,
/// cross_launch_arch)`. A process target that is neither launch arch cannot
/// honestly stand in for a launch arch dimension, so we refuse.
fn native_launch_arch() -> Result<(&'static str, &'static str)> {
    match env::consts::ARCH {
        "aarch64" => Ok(("aarch64", "x86_64")),
        "x86_64" => Ok(("x86_64", "aarch64")),
        other => bail!(
            "effective process architecture `{other}` is neither launch-critical arch (aarch64, x86_64); this native host check cannot stand in for a launch arch dimension"
        ),
    }
}

/// Architecture component of a target triple (the text before the first `-`).
fn triple_arch(triple: &str) -> &str {
    triple.split('-').next().unwrap_or(triple)
}

/// Discover the unique, validated repo-local stage2 Trust compiler. An ambient
/// `TRUSTC` is intentionally ignored: only `build/<host>/stage2/bin/trustc` is
/// launch evidence.
fn locate_trustc(root: &Path) -> Result<PathBuf> {
    match find_stage2_tool(root, "trustc")? {
        Some(trustc) => Ok(trustc),
        None => bail!(
            "ERROR (setup): unique repo-local stage2 Trust compiler not found under build/*/stage2/bin; build it with `./x.py build --stage 2`"
        ),
    }
}

/// Read `trustc -vV` and return the reported `host:` triple.
fn toolchain_host_triple(trustc: &Path, cwd: &Path) -> Result<String> {
    let mut command = trustc_command(trustc, cwd)?;
    command.arg("-vV");
    let captured = capture(command)?;
    if !captured.exited_with(0) {
        bail!(
            "`trustc -vV` exited with status {}\nstdout:\n{}\nstderr:\n{}",
            captured.exit,
            captured.stdout,
            captured.stderr
        );
    }
    for line in captured.stdout.lines() {
        if let Some(rest) = line.strip_prefix("host: ") {
            let triple = rest.trim();
            if triple.is_empty() {
                bail!("`trustc -vV` emitted an empty host triple");
            }
            return Ok(triple.to_string());
        }
    }
    bail!("`trustc -vV` did not report a host triple\nstdout:\n{}", captured.stdout)
}

/// A `trustc` invocation with the compiler-injection env scrubbed and the
/// sysroot's own runtime libraries on the loader path so a bare stage2 `trustc`
/// can load its driver dylibs. No inherited loader path is ever merged in.
fn trustc_command(trustc: &Path, cwd: &Path) -> Result<Command> {
    trustc_native::trustc_command(trustc, cwd)
}

/// Run the freshly-compiled host binary. The compiler-injection env is
/// scrubbed; the sysroot runtime dirs are added defensively in case std was
/// linked dynamically.
fn run_host_binary(binary: &Path, trustc: &Path, cwd: &Path) -> Result<Captured> {
    let mut command = Command::new(binary);
    command.current_dir(cwd);
    scrub_gate_process_environment(&mut command);
    trustc_native::apply_trusted_runtime_library_path(&mut command, trustc)?;
    capture(command)
}

fn is_executable_file(path: &Path) -> bool {
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt as _;
        fs::symlink_metadata(path)
            .is_ok_and(|meta| meta.file_type().is_file() && meta.permissions().mode() & 0o111 != 0)
    }
    #[cfg(not(unix))]
    {
        fs::symlink_metadata(path).is_ok_and(|meta| meta.file_type().is_file())
    }
}

/// Classify the object-file header and report whether its machine type encodes
/// `native_arch`. Recognizes ELF, Mach-O (thin, either endianness), and PE/COFF.
/// An unrecognized format is an error (never a silent pass).
fn binary_arch_matches(bytes: &[u8], native_arch: &str) -> Result<bool> {
    // ELF: e_machine is a u16 at offset 18; EI_DATA at offset 5 (2 = big-endian).
    if bytes.starts_with(&[0x7f, b'E', b'L', b'F']) {
        if bytes.get(4) != Some(&2u8) || bytes.get(6) != Some(&1u8) {
            bail!("launch evidence requires a version-1 64-bit ELF object");
        }
        let little = match bytes.get(5) {
            Some(1) => true,
            Some(2) => false,
            other => bail!("ELF header has invalid EI_DATA value {other:?}"),
        };
        let machine =
            read_u16(bytes, 18, little).context("ELF header truncated before e_machine")?;
        let expected = match native_arch {
            "aarch64" => 183u16, // EM_AARCH64
            "x86_64" => 62,      // EM_X86_64
            _ => return Ok(false),
        };
        return Ok(machine == expected);
    }

    // Thin 64-bit Mach-O, little- or big-endian; cputype is at offset 4.
    let head = bytes.get(0..4);
    let macho_le = matches!(head, Some(&[0xcf, 0xfa, 0xed, 0xfe]));
    let macho_be = matches!(head, Some(&[0xfe, 0xed, 0xfa, 0xcf]));
    if macho_le || macho_be {
        let cputype =
            read_u32(bytes, 4, macho_le).context("Mach-O header truncated before cputype")?;
        let expected = match native_arch {
            "aarch64" => 0x0100_000Cu32, // CPU_TYPE_ARM64
            "x86_64" => 0x0100_0007,     // CPU_TYPE_X86_64
            _ => return Ok(false),
        };
        return Ok(cputype == expected);
    }

    // PE/COFF: "MZ", then a u32 LE offset at 0x3C to the "PE\0\0" signature; the
    // COFF machine u16 follows the signature.
    if bytes.starts_with(b"MZ") {
        let pe_off =
            read_u32(bytes, 0x3c, true).context("PE header offset field truncated")? as usize;
        if let Some(rest) = bytes.get(pe_off..) {
            if rest.starts_with(b"PE\0\0") {
                let machine = read_u16(rest, 4, true).context("PE COFF machine field truncated")?;
                let expected = match native_arch {
                    "aarch64" => 0xAA64u16, // IMAGE_FILE_MACHINE_ARM64
                    "x86_64" => 0x8664,     // IMAGE_FILE_MACHINE_AMD64
                    _ => return Ok(false),
                };
                return Ok(machine == expected);
            }
        }
    }

    bail!(
        "emitted executable has an unrecognized object-file format (first bytes: {:02x?})",
        bytes.get(0..bytes.len().min(8)).unwrap_or_default()
    )
}

fn read_u16(bytes: &[u8], offset: usize, little_endian: bool) -> Option<u16> {
    let slice = bytes.get(offset..offset.checked_add(2)?)?;
    let array = [slice[0], slice[1]];
    Some(if little_endian { u16::from_le_bytes(array) } else { u16::from_be_bytes(array) })
}

fn read_u32(bytes: &[u8], offset: usize, little_endian: bool) -> Option<u32> {
    let slice = bytes.get(offset..offset.checked_add(4)?)?;
    let array = [slice[0], slice[1], slice[2], slice[3]];
    Some(if little_endian { u32::from_le_bytes(array) } else { u32::from_be_bytes(array) })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn triple_arch_takes_first_component() {
        assert_eq!(triple_arch("aarch64-apple-darwin"), "aarch64");
        assert_eq!(triple_arch("x86_64-unknown-linux-gnu"), "x86_64");
        assert_eq!(triple_arch("standalone"), "standalone");
    }

    #[test]
    fn native_launch_arch_is_a_launch_arch_on_supported_hosts() {
        // The CI/dev hosts this ever runs on are aarch64 or x86_64.
        let (host, cross) = native_launch_arch().expect("host is a launch arch");
        assert_ne!(host, cross);
        assert!(matches!(host, "aarch64" | "x86_64"));
        assert!(matches!(cross, "aarch64" | "x86_64"));
    }

    #[test]
    fn elf_machine_type_is_classified() {
        let mut elf = vec![0u8; 20];
        elf[0..4].copy_from_slice(&[0x7f, b'E', b'L', b'F']);
        elf[4] = 2; // 64-bit
        elf[5] = 1; // little-endian
        elf[6] = 1; // version
        elf[18..20].copy_from_slice(&62u16.to_le_bytes()); // EM_X86_64
        assert!(binary_arch_matches(&elf, "x86_64").unwrap());
        assert!(!binary_arch_matches(&elf, "aarch64").unwrap());

        elf[4] = 1; // 32-bit class cannot represent either launch architecture.
        assert!(binary_arch_matches(&elf, "x86_64").is_err());
        elf[4] = 2;
        elf[5] = 0; // Invalid/unspecified byte order must not be guessed.
        assert!(binary_arch_matches(&elf, "x86_64").is_err());
    }

    #[test]
    fn macho_arm64_cputype_is_classified() {
        let mut macho = vec![0u8; 8];
        macho[0..4].copy_from_slice(&[0xcf, 0xfa, 0xed, 0xfe]); // MH_MAGIC_64, LE
        macho[4..8].copy_from_slice(&0x0100_000Cu32.to_le_bytes()); // CPU_TYPE_ARM64
        assert!(binary_arch_matches(&macho, "aarch64").unwrap());
        assert!(!binary_arch_matches(&macho, "x86_64").unwrap());

        macho[0..4].copy_from_slice(&[0xce, 0xfa, 0xed, 0xfe]); // 32-bit magic
        assert!(binary_arch_matches(&macho, "aarch64").is_err());
    }

    #[test]
    fn pe_machine_type_is_classified() {
        // "MZ", PE offset at 0x3C -> 0x40, then "PE\0\0" and IMAGE_FILE_MACHINE_AMD64.
        let mut pe = vec![0u8; 0x48];
        pe[0..2].copy_from_slice(b"MZ");
        pe[0x3c..0x40].copy_from_slice(&0x40u32.to_le_bytes());
        pe[0x40..0x44].copy_from_slice(b"PE\0\0");
        pe[0x44..0x46].copy_from_slice(&0x8664u16.to_le_bytes());
        assert!(binary_arch_matches(&pe, "x86_64").unwrap());
        assert!(!binary_arch_matches(&pe, "aarch64").unwrap());
    }

    #[test]
    fn unrecognized_object_format_is_an_error() {
        assert!(binary_arch_matches(&[0x00, 0x01, 0x02, 0x03], "x86_64").is_err());
        assert!(binary_arch_matches(&[], "aarch64").is_err());
    }

    #[test]
    fn bounded_integer_reads_reject_truncation() {
        assert_eq!(read_u16(&[0x01], 0, true), None);
        assert_eq!(read_u16(&[0x01, 0x02], 0, true), Some(0x0201));
        assert_eq!(read_u32(&[0x01, 0x02, 0x03], 0, true), None);
        assert_eq!(read_u32(&[0x01, 0x00, 0x00, 0x00], 0, true), Some(1));
    }
}
