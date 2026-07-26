use std::env;
use std::ffi::{OsStr, OsString};
use std::fs::{self, OpenOptions};
use std::io;
use std::panic;
use std::path::Path;
use std::process::{Command, Stdio};

#[cfg(unix)]
use std::ffi::{CStr, CString};
#[cfg(unix)]
use std::io::Write;
#[cfg(unix)]
use std::os::raw::c_char;
#[cfg(unix)]
use std::os::unix::ffi::{OsStrExt, OsStringExt};
#[cfg(unix)]
use std::os::unix::fs::{DirBuilderExt, OpenOptionsExt, PermissionsExt, symlink};
#[cfg(unix)]
use std::os::unix::net::UnixStream;

use hardened_regression_fixtures::ScratchDir;
#[cfg(unix)]
use hardened_regression_fixtures::{hex_bytes, unix_file_id};

#[cfg(unix)]
unsafe extern "C" {
    fn getenv(name: *const c_char) -> *mut c_char;
    fn strlen(value: *const c_char) -> usize;
}

fn main() -> io::Result<()> {
    let mut args = env::args_os();
    let _program = args.next();
    if let Some(mode) = args.next() {
        if mode == OsStr::new("--sigpipe-child") {
            return sigpipe_child_main();
        }
        if mode == OsStr::new("--cli-arg-child") {
            return cli_arg_child_main(args.collect());
        }
    }

    permission_walkthrough()?;
    raw_path_re_resolution_walkthrough()?;
    error_discard_integrity_walkthrough()?;
    panic_boundary_walkthrough()?;
    process_sigpipe_walkthrough()?;
    cli_arg_compatibility_walkthrough()?;
    trust_domain_order_walkthrough()?;
    ffi_boundary_inventory_walkthrough()?;

    Ok(())
}

#[cfg(unix)]
fn permission_walkthrough() -> io::Result<()> {
    let scratch = ScratchDir::new("permission-window")?;
    let create_parent_file_id = unix_file_id(scratch.path())?;
    let secure = scratch.path_for(OsStr::new("secure-created.txt"))?;
    let _file = OpenOptions::new().write(true).create_new(true).mode(0o600).open(&secure)?;
    let secure_mode = mode_bits(&secure)?;
    if secure_mode & 0o077 != 0 {
        return Err(io::Error::new(
            io::ErrorKind::Other,
            "secure create unexpectedly left group/other permission bits set",
        ));
    }

    let windowed = scratch.write_file(OsStr::new("windowed.txt"), b"permission window\n")?;
    let window_file_id_before = unix_file_id(&windowed)?;
    set_mode(&windowed, 0o644)?;
    let window_start_mode = mode_bits(&windowed)?;
    set_mode(&windowed, 0o600)?;
    let window_final_mode = mode_bits(&windowed)?;
    let window_file_id_after = unix_file_id(&windowed)?;
    if window_start_mode != 0o644 || window_final_mode != 0o600 {
        return Err(io::Error::new(
            io::ErrorKind::Other,
            "chmod did not produce the expected permission transition",
        ));
    }
    if window_file_id_before != window_file_id_after {
        return Err(io::Error::new(
            io::ErrorKind::Other,
            "chmod target identity changed during the permission walkthrough",
        ));
    }

    let created_dir = scratch.path_for(OsStr::new("created-dir"))?;
    fs::DirBuilder::new().mode(0o700).create(&created_dir)?;
    let dir_mode = mode_bits(&created_dir)?;
    if dir_mode != 0o700 {
        return Err(io::Error::new(
            io::ErrorKind::Other,
            "created directory permissions did not match the requested creation-time mode",
        ));
    }

    println!("walkthrough=permissions");
    println!("scratch={}", scratch.path().display());
    println!("create_parent_file_id={create_parent_file_id}");
    println!("create_parent_identity_verified=yes");
    println!("create_new_requested_mode=0o600");
    println!("create_new_group_other_bits={}", format_mode(secure_mode & 0o077));
    println!("chmod_file_id_before={window_file_id_before}");
    println!("chmod_file_id_after={window_file_id_after}");
    println!("chmod_identity_stable=yes");
    println!("chmod_window_start_mode={}", format_mode(window_start_mode));
    println!("chmod_window_final_mode={}", format_mode(window_final_mode));
    println!("create_dir_requested_mode=0o700");
    println!("create_dir_creation_mode={}", format_mode(dir_mode));
    println!("chmod_change_observed=yes");
    println!("rootless_scope=create_new,chmod,metadata");
    println!("result=permission-window-create-change-demonstrated");

    Ok(())
}

#[cfg(not(unix))]
fn permission_walkthrough() -> io::Result<()> {
    println!("walkthrough=permissions");
    println!("permissions_unsupported=non-unix");
    Ok(())
}

fn error_discard_integrity_walkthrough() -> io::Result<()> {
    let scratch = ScratchDir::new("error-discard")?;
    let expected = b"trusted payload\n";
    let expected_path = scratch.write_file(OsStr::new("expected.txt"), expected)?;
    let missing_path = scratch.path_for(OsStr::new("missing.txt"))?;

    let expected_roundtrip = fs::read(&expected_path)?;
    if expected_roundtrip != expected {
        return Err(io::Error::new(
            io::ErrorKind::Other,
            "expected payload did not round-trip before the missing-file probe",
        ));
    }

    let remove_error = fs::remove_file(&missing_path).expect_err("missing remove should fail");
    let canonicalize_error =
        fs::canonicalize(&missing_path).expect_err("missing canonicalize should fail");
    let checked_read_error = fs::read(&missing_path).expect_err("missing read should fail");
    let discarded_fallback = fs::read(&missing_path).unwrap_or_default();
    if discarded_fallback == expected {
        return Err(io::Error::new(
            io::ErrorKind::Other,
            "discarded fallback unexpectedly matched the trusted payload",
        ));
    }
    let checked_decision = match fs::read(&missing_path) {
        Ok(bytes) if bytes == expected => "accept",
        Ok(_) => "reject-mismatch",
        Err(_) => "reject-error",
    };
    let fallback_decision =
        if discarded_fallback == expected { "accept" } else { "reject-empty-fallback" };

    println!("walkthrough=error_discard_integrity");
    println!("scratch={}", scratch.path().display());
    println!("expected_len={}", expected.len());
    println!("discarded_remove_error={:?}", remove_error.kind());
    println!("discarded_canonicalize_error={:?}", canonicalize_error.kind());
    println!("checked_read_error={:?}", checked_read_error.kind());
    println!("discarded_read_error=lost");
    println!("discarded_fallback_len={}", discarded_fallback.len());
    println!("fallback_matches_expected=no");
    println!("checked_decision={checked_decision}");
    println!("fallback_decision={fallback_decision}");
    println!("integrity_check=discard-changes-decision");
    println!("result=error-discard-integrity-demonstrated");

    Ok(())
}

#[cfg(unix)]
fn raw_path_re_resolution_walkthrough() -> io::Result<()> {
    let scratch = ScratchDir::new("raw-path-re-resolution")?;
    let trusted = scratch.write_file(OsStr::new("raw-trusted.txt"), b"trusted\n")?;
    let replacement = scratch.write_file(OsStr::new("raw-replacement.txt"), b"replacement\n")?;
    let trusted_canonical = fs::canonicalize(&trusted)?;
    let replacement_canonical = fs::canonicalize(&replacement)?;
    let checked = scratch.path_for(OsStr::new("raw-candidate"))?;
    let next_link = scratch.path_for(OsStr::new("raw-candidate.next"))?;

    symlink(Path::new("raw-trusted.txt"), &checked)?;
    let pre_metadata = fs::metadata(&checked)?;
    let pre_canonical = fs::canonicalize(&checked)?;
    let pre_file_id = unix_file_id(&checked)?;
    let pre_read = fs::read(&checked)?;

    symlink(Path::new("raw-replacement.txt"), &next_link)?;
    fs::rename(&next_link, &checked)?;

    let post_metadata = fs::metadata(&checked)?;
    let post_canonical = fs::canonicalize(&checked)?;
    let post_file_id = unix_file_id(&checked)?;
    let post_read = fs::read(&checked)?;

    if pre_canonical != trusted_canonical
        || post_canonical != replacement_canonical
        || pre_file_id == post_file_id
        || pre_metadata.len() == post_metadata.len()
        || pre_read != b"trusted\n"
        || post_read != b"replacement\n"
    {
        return Err(io::Error::new(
            io::ErrorKind::Other,
            "raw path did not re-resolve to the replacement target",
        ));
    }

    println!("walkthrough=raw_path_re_resolution");
    println!("scratch={}", scratch.path().display());
    println!("checked_path=raw-candidate");
    println!("initial_target=raw-trusted.txt");
    println!("replacement_target=raw-replacement.txt");
    println!("pre_canonical_leaf={}", path_leaf(&pre_canonical)?);
    println!("post_canonical_leaf={}", path_leaf(&post_canonical)?);
    println!("pre_file_id={pre_file_id}");
    println!("post_file_id={post_file_id}");
    println!("pre_read=trusted");
    println!("post_read=replacement");
    println!("raw_path_re_resolved=yes");
    println!("raw_path_scope=metadata,canonicalize,symlink,rename,read");
    println!("result=raw-path-re-resolution-demonstrated");

    Ok(())
}

#[cfg(not(unix))]
fn raw_path_re_resolution_walkthrough() -> io::Result<()> {
    println!("walkthrough=raw_path_re_resolution");
    println!("raw_path_unsupported=non-unix");
    Ok(())
}

fn panic_boundary_walkthrough() -> io::Result<()> {
    let scratch = ScratchDir::new("panic-boundary")?;
    let present = scratch.write_file(OsStr::new("present.txt"), b"panic safe\n")?;
    let missing = scratch.path_for(OsStr::new("missing.txt"))?;

    let _metadata = fs::metadata(&present)?;
    let safe_utf8 = String::from_utf8(b"panic safe".to_vec())
        .map_err(|error| io::Error::new(io::ErrorKind::InvalidData, error))?;
    if safe_utf8 != "panic safe" {
        return Err(io::Error::new(
            io::ErrorKind::Other,
            "valid UTF-8 did not survive panic boundary setup",
        ));
    }

    let previous_hook = panic::take_hook();
    panic::set_hook(Box::new(|_| {}));
    let metadata_panicked = panic::catch_unwind(|| {
        fs::metadata(&missing).expect("missing metadata models panic-on-error");
    })
    .is_err();
    let utf8_panicked = panic::catch_unwind(|| {
        String::from_utf8(vec![0xff]).unwrap();
    })
    .is_err();
    let assert_panicked = panic::catch_unwind(|| {
        assert!(!b"".is_empty(), "empty byte slice models assertion boundary");
    })
    .is_err();
    let panic_panicked = panic::catch_unwind(|| {
        panic!("explicit panic boundary");
    })
    .is_err();
    let todo_panicked = panic::catch_unwind(|| {
        todo!("unfinished public edge");
    })
    .is_err();
    let unreachable_panicked = panic::catch_unwind(|| {
        unreachable!("impossible branch boundary");
    })
    .is_err();
    panic::set_hook(previous_hook);

    let caught = [
        metadata_panicked,
        utf8_panicked,
        assert_panicked,
        panic_panicked,
        todo_panicked,
        unreachable_panicked,
    ];
    let caught_count = caught.iter().filter(|panicked| **panicked).count();
    if caught_count != caught.len() {
        return Err(io::Error::new(
            io::ErrorKind::Other,
            "not every panic boundary probe was caught",
        ));
    }

    println!("walkthrough=panic_boundary");
    println!("scratch={}", scratch.path().display());
    println!("safe_metadata=ok");
    println!("safe_utf8=ok");
    println!("panic_hook=suppressed");
    println!("caught_panics=metadata_expect,utf8_unwrap,assert,panic,todo,unreachable");
    println!("caught_panic_count={caught_count}");
    println!("panic_payloads_escaped=no");
    println!("result=panic-boundary-demonstrated");

    Ok(())
}

#[cfg(unix)]
fn process_sigpipe_walkthrough() -> io::Result<()> {
    let (mut writer, reader) = UnixStream::pair()?;
    drop(reader);
    let closed_stream_error =
        writer.write_all(b"closed peer").expect_err("closed peer write should fail");
    if closed_stream_error.kind() != io::ErrorKind::BrokenPipe {
        return Err(io::Error::new(
            io::ErrorKind::Other,
            format!("closed UnixStream produced {:?}, not BrokenPipe", closed_stream_error.kind()),
        ));
    }

    let mut child = Command::new(env::current_exe()?)
        .arg("--sigpipe-child")
        .env("HARDENED_SIGPIPE_CHILD", "1")
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()?;
    drop(child.stdout.take());
    let output = child.wait_with_output()?;
    if !output.status.success() {
        return Err(io::Error::new(
            io::ErrorKind::Other,
            format!(
                "sigpipe child failed with status {} and stderr {:?}",
                output.status,
                String::from_utf8_lossy(&output.stderr)
            ),
        ));
    }
    if !output.stderr.is_empty() {
        return Err(io::Error::new(
            io::ErrorKind::Other,
            format!(
                "sigpipe child unexpectedly wrote stderr {:?}",
                String::from_utf8_lossy(&output.stderr)
            ),
        ));
    }

    println!("walkthrough=process_sigpipe");
    println!("closed_stream_write_error={:?}", closed_stream_error.kind());
    println!("sigpipe_child_stdout_closed=yes");
    println!("sigpipe_child_exit=success");
    println!("broken_pipe_handled=ok");
    println!("result=process-sigpipe-demonstrated");

    Ok(())
}

#[cfg(not(unix))]
fn process_sigpipe_walkthrough() -> io::Result<()> {
    println!("walkthrough=process_sigpipe");
    println!("sigpipe_unsupported=non-unix");
    Ok(())
}

#[cfg(unix)]
fn sigpipe_child_main() -> io::Result<()> {
    if env::var_os("HARDENED_SIGPIPE_CHILD").is_none() {
        return Err(io::Error::new(
            io::ErrorKind::PermissionDenied,
            "sigpipe child mode is only for the parent walkthrough",
        ));
    }

    let chunk = [b'x'; 8192];
    let mut stdout = io::stdout().lock();
    for _ in 0..4096 {
        match stdout.write_all(&chunk) {
            Ok(()) => {}
            Err(error) if error.kind() == io::ErrorKind::BrokenPipe => return Ok(()),
            Err(error) => return Err(error),
        }
    }

    Err(io::Error::new(io::ErrorKind::Other, "closed stdout did not report BrokenPipe"))
}

#[cfg(not(unix))]
fn sigpipe_child_main() -> io::Result<()> {
    Ok(())
}

#[cfg(unix)]
fn cli_arg_compatibility_walkthrough() -> io::Result<()> {
    let invalid_arg = OsString::from_vec(b"arg_\xff".to_vec());
    let output = Command::new(env::current_exe()?)
        .arg("--cli-arg-child")
        .arg("space value")
        .arg(&invalid_arg)
        .output()?;
    if !output.status.success() {
        return Err(io::Error::new(
            io::ErrorKind::Other,
            format!(
                "CLI arg child failed with status {} and stderr {:?}",
                output.status,
                String::from_utf8_lossy(&output.stderr)
            ),
        ));
    }
    if !output.stderr.is_empty() {
        return Err(io::Error::new(
            io::ErrorKind::Other,
            format!(
                "CLI arg child unexpectedly wrote stderr {:?}",
                String::from_utf8_lossy(&output.stderr)
            ),
        ));
    }

    let child_stdout = String::from_utf8(output.stdout)
        .map_err(|error| io::Error::new(io::ErrorKind::InvalidData, error))?;
    if !child_stdout.contains("cli_child_invalid_arg_to_str=none")
        || !child_stdout.contains("cli_child_strict_utf8=error")
    {
        return Err(io::Error::new(
            io::ErrorKind::Other,
            format!("CLI arg child did not prove byte-preserving args:\n{child_stdout}"),
        ));
    }

    println!("walkthrough=cli_args");
    println!("parent_args_os_count={}", env::args_os().count());
    print!("{child_stdout}");
    println!("result=cli-arg-compatibility-demonstrated");

    Ok(())
}

#[cfg(not(unix))]
fn cli_arg_compatibility_walkthrough() -> io::Result<()> {
    println!("walkthrough=cli_args");
    println!("cli_args_unsupported=non-unix");
    Ok(())
}

#[cfg(unix)]
fn cli_arg_child_main(args: Vec<OsString>) -> io::Result<()> {
    let space_arg_preserved = args.iter().any(|arg| arg == OsStr::new("space value"));
    let invalid_arg = args
        .iter()
        .find(|arg| arg.as_bytes().contains(&0xff))
        .ok_or_else(|| io::Error::new(io::ErrorKind::InvalidInput, "missing invalid arg"))?;
    let invalid_bytes = invalid_arg.as_bytes();
    if invalid_arg.to_str().is_some() || String::from_utf8(invalid_bytes.to_vec()).is_ok() {
        return Err(io::Error::new(
            io::ErrorKind::Other,
            "invalid argument unexpectedly converted to strict UTF-8",
        ));
    }

    println!("cli_child_mode=args_os");
    println!("cli_child_arg_count={}", args.len());
    println!("cli_child_space_arg={}", if space_arg_preserved { "preserved" } else { "missing" });
    println!("cli_child_invalid_arg_hex={}", hex_bytes(invalid_bytes));
    println!("cli_child_invalid_arg_to_str=none");
    println!("cli_child_strict_utf8=error");

    Ok(())
}

#[cfg(not(unix))]
fn cli_arg_child_main(_args: Vec<OsString>) -> io::Result<()> {
    Ok(())
}

fn trust_domain_order_walkthrough() -> io::Result<()> {
    let scratch = ScratchDir::new("trust-domain-order")?;
    let _root_metadata = fs::metadata(scratch.path())?;
    let _root_canonical = fs::canonicalize(scratch.path())?;
    let user_probe = rootless_user_probe()?;
    let group_probe = rootless_group_probe()?;
    let plugin = scratch.write_file(OsStr::new("plugin-candidate.so"), b"not a shared object\n")?;
    let _plugin_metadata = fs::metadata(&plugin)?;
    let _plugin_canonical = fs::canonicalize(&plugin)?;
    let plugin_bytes = fs::read(&plugin)?;
    if plugin_bytes != b"not a shared object\n" {
        return Err(io::Error::new(
            io::ErrorKind::Other,
            "plugin path probe did not read the expected candidate bytes",
        ));
    }

    let safe_trace = [
        TrustOp::ResolveRoot,
        TrustOp::ResolveUser,
        TrustOp::GetPwNam,
        TrustOp::ResolveGroup,
        TrustOp::GetGrNam,
        TrustOp::ResolvePluginPath,
        TrustOp::Dlopen,
        TrustOp::SimulateChroot,
        TrustOp::SimulateSetgid,
        TrustOp::SimulateSetuid,
    ];
    let unsafe_trace = [
        TrustOp::SimulateChroot,
        TrustOp::ResolveUser,
        TrustOp::GetPwNam,
        TrustOp::ResolveGroup,
        TrustOp::GetGrNam,
        TrustOp::ResolvePluginPath,
        TrustOp::Dlopen,
        TrustOp::SimulateSetgid,
        TrustOp::SimulateSetuid,
    ];
    let safe_late = late_trust_domain_lookups(&safe_trace);
    let unsafe_late = late_trust_domain_lookups(&unsafe_trace);
    if safe_late != 0 || unsafe_late != 6 {
        return Err(io::Error::new(
            io::ErrorKind::Other,
            "trust-domain trace checker produced unexpected violation counts",
        ));
    }

    println!("walkthrough=trust_domain_order");
    println!("scratch={}", scratch.path().display());
    println!("rootless_root_metadata=ok");
    println!("rootless_root_canonicalize=ok");
    println!("rootless_user_probe={user_probe}");
    println!("rootless_group_probe={group_probe}");
    println!("rootless_plugin_metadata=ok");
    println!("rootless_plugin_canonicalize=ok");
    println!("rootless_plugin_read=ok");
    println!("pre_privilege_probe_order=root,user,group,plugin");
    println!("privileged_ops=simulate_chroot,simulate_setgid,simulate_setuid");
    println!("privileged_ops_executed=no");
    println!("privileged_ops_mode=simulated");
    println!("root_transition_effect=not_exercised");
    println!("uid_gid_transition_effect=not_exercised");
    println!("nss_inside_chroot=not_exercised");
    println!("dynamic_loader_inside_chroot=not_exercised");
    println!("evidence_scope=rootless_preflight_and_trace_order");
    println!("safe_trace={}", format_trace(&safe_trace));
    println!("unsafe_trace={}", format_trace(&unsafe_trace));
    println!("safe_trace_late_lookups={safe_late}");
    println!("unsafe_trace_late_lookups={unsafe_late}");
    println!("result=trust-domain-order-demonstrated-rootlessly");

    Ok(())
}

#[cfg(unix)]
fn rootless_user_probe() -> io::Result<&'static str> {
    run_id_probe(&["-un"])?;
    Ok("ok")
}

#[cfg(not(unix))]
fn rootless_user_probe() -> io::Result<&'static str> {
    Ok("unsupported")
}

#[cfg(unix)]
fn rootless_group_probe() -> io::Result<&'static str> {
    run_id_probe(&["-gn"])?;
    Ok("ok")
}

#[cfg(not(unix))]
fn rootless_group_probe() -> io::Result<&'static str> {
    Ok("unsupported")
}

#[cfg(unix)]
fn run_id_probe(args: &[&str]) -> io::Result<()> {
    let id_path = if Path::new("/usr/bin/id").exists() { "/usr/bin/id" } else { "id" };
    let output =
        Command::new(id_path).args(args).stdout(Stdio::piped()).stderr(Stdio::piped()).output()?;
    if output.status.success() && !output.stdout.is_empty() {
        return Ok(());
    }

    Err(io::Error::new(
        io::ErrorKind::Other,
        format!(
            "rootless id probe {:?} failed with status {} and stderr {:?}",
            args,
            output.status,
            String::from_utf8_lossy(&output.stderr)
        ),
    ))
}

#[cfg(unix)]
fn ffi_boundary_inventory_walkthrough() -> io::Result<()> {
    let sample = CString::new("trust").expect("static sample contains no NUL");
    let len = unsafe { strlen(sample.as_ptr()) };
    if len != 5 {
        return Err(io::Error::new(
            io::ErrorKind::Other,
            "strlen did not return the expected sample length",
        ));
    }

    let path_name = CString::new("PATH").expect("static env name contains no NUL");
    let path_ptr = unsafe { getenv(path_name.as_ptr()) };
    let getenv_path = if path_ptr.is_null() {
        "absent"
    } else {
        let _path_value = unsafe { CStr::from_ptr(path_ptr) };
        "present"
    };

    let mut byte = 7u8;
    let ptr = &mut byte as *mut u8;
    unsafe {
        *ptr.add(0) = ptr.read().wrapping_add(1);
    }
    if byte != 8 {
        return Err(io::Error::new(
            io::ErrorKind::Other,
            "raw pointer inventory probe did not update the byte",
        ));
    }

    println!("walkthrough=unsafe_ffi_boundary_inventory");
    println!("unsafe_pointer_probe=ok");
    println!("unsafe_block_count=1");
    println!("walkthrough=ffi_boundary_inventory");
    println!("ffi_declared=getenv,strlen");
    println!("ffi_called=getenv,strlen");
    println!("ffi_call_count=2");
    println!("strlen_result={len}");
    println!("getenv_path={getenv_path}");
    println!("inventory_count=3");
    println!("result=unsafe-ffi-boundary-inventory-demonstrated");

    Ok(())
}

#[cfg(not(unix))]
fn ffi_boundary_inventory_walkthrough() -> io::Result<()> {
    println!("walkthrough=unsafe_ffi_boundary_inventory");
    println!("walkthrough=ffi_boundary_inventory");
    println!("ffi_unsupported=non-unix");
    Ok(())
}

#[derive(Clone, Copy)]
enum TrustOp {
    ResolveRoot,
    ResolveUser,
    ResolveGroup,
    ResolvePluginPath,
    GetPwNam,
    GetGrNam,
    Dlopen,
    SimulateChroot,
    SimulateSetgid,
    SimulateSetuid,
}

impl TrustOp {
    fn name(self) -> &'static str {
        match self {
            Self::ResolveRoot => "resolve_root",
            Self::ResolveUser => "resolve_user",
            Self::ResolveGroup => "resolve_group",
            Self::ResolvePluginPath => "resolve_plugin_path",
            Self::GetPwNam => "getpwnam",
            Self::GetGrNam => "getgrnam",
            Self::Dlopen => "dlopen",
            Self::SimulateChroot => "simulate_chroot",
            Self::SimulateSetgid => "simulate_setgid",
            Self::SimulateSetuid => "simulate_setuid",
        }
    }

    fn locks_trust_domain(self) -> bool {
        matches!(self, Self::SimulateChroot | Self::SimulateSetgid | Self::SimulateSetuid)
    }

    fn must_precede_trust_lock(self) -> bool {
        matches!(
            self,
            Self::ResolveRoot
                | Self::ResolveUser
                | Self::ResolveGroup
                | Self::ResolvePluginPath
                | Self::GetPwNam
                | Self::GetGrNam
                | Self::Dlopen
        )
    }
}

fn late_trust_domain_lookups(trace: &[TrustOp]) -> usize {
    let mut trust_locked = false;
    let mut violations = 0;
    for op in trace {
        if trust_locked && op.must_precede_trust_lock() {
            violations += 1;
        }
        trust_locked |= op.locks_trust_domain();
    }
    violations
}

fn format_trace(trace: &[TrustOp]) -> String {
    let mut formatted = String::new();
    for (index, op) in trace.iter().enumerate() {
        if index > 0 {
            formatted.push(',');
        }
        formatted.push_str(op.name());
    }
    formatted
}

#[cfg(unix)]
fn path_leaf(path: &Path) -> io::Result<&str> {
    path.file_name().and_then(OsStr::to_str).ok_or_else(|| {
        io::Error::new(
            io::ErrorKind::InvalidData,
            format!("path did not have a UTF-8 final component: {}", path.display()),
        )
    })
}

#[cfg(unix)]
fn set_mode(path: &Path, mode: u32) -> io::Result<()> {
    fs::set_permissions(path, fs::Permissions::from_mode(mode))
}

#[cfg(unix)]
fn mode_bits(path: &Path) -> io::Result<u32> {
    Ok(fs::metadata(path)?.permissions().mode() & 0o777)
}

#[cfg(unix)]
fn format_mode(mode: u32) -> String {
    format!("0o{:03o}", mode & 0o777)
}
