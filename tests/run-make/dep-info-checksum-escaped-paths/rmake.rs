//@ ignore-cross-compile
//@ needs-target-std

// Trust: filesystem paths must remain raw until after their checksums are computed.
use run_make_support::{rfs, rustc};

fn checksum<'a>(dep_info: &'a str, path: &str) -> &'a str {
    let escaped = path.replace(' ', "\\ ");
    let suffix = format!(" {escaped}");
    dep_info
        .lines()
        .find(|line| line.starts_with("# checksum:") && line.ends_with(&suffix))
        .unwrap_or_else(|| panic!("missing checksum for {path:?}:\n{dep_info}"))
        .strip_suffix(&suffix)
        .unwrap()
}

fn compile(output: &str, dependency: &str) -> String {
    rustc()
        .input("consumer.rs")
        .crate_type("lib")
        .extern_("helper", dependency)
        .args(["-Zchecksum-hash-algorithm=sha256", "-Zbinary-dep-depinfo"])
        .emit("dep-info")
        .output(output)
        .run()
        .assert_stderr_not_contains("failed to compute checksum");
    rfs::read_to_string(output)
}

// Trust: the old escaped lookup must find different bytes, not merely a missing file.
#[cfg(unix)]
fn escaped_decoy(path: &str) {
    let escaped = path.replace(' ', "\\ ");
    assert_ne!(escaped, path);
    let escaped = std::path::Path::new(&escaped);
    if let Some(parent) = escaped.parent().filter(|p| !p.as_os_str().is_empty()) {
        rfs::create_dir_all(parent);
    }
    rfs::write(escaped, b"different escaped-path decoy bytes\n");
}

fn main() {
    let contents = b"# identical tracked bytes\n";
    rfs::write("plain.txt", contents);
    rfs::create_dir_all("nested dir");
    let mut paths = vec!["input with spaces.txt", "nested dir/Unicode Ω input.txt"];
    if cfg!(unix) {
        paths.push("nested dir/literal\\slash with spaces.txt");
    }
    for path in &paths {
        rfs::write(path, contents);
    }
    let visualizer = "nested dir/debugger script.py";
    rfs::write(visualizer, contents);
    #[cfg(unix)]
    for path in paths.iter().copied().chain([visualizer]) {
        escaped_decoy(path);
    }
    let mut source = format!(
        "#![debugger_visualizer(gdb_script_file = {visualizer:?})]\n\
         extern crate helper;\n\
         pub fn answer() -> u8 {{ helper::answer() }}\n\
         pub static PLAIN: &[u8] = include_bytes!(\"plain.txt\");\n"
    );
    for (i, path) in paths.iter().enumerate() {
        source.push_str(&format!("pub static INPUT_{i}: &[u8] = include_bytes!({path:?});\n"));
    }
    rfs::write("consumer.rs", source);
    rfs::write("helper.rs", "pub fn answer() -> u8 { 42 }\n");
    rfs::create_dir_all("deps with spaces");
    let binary = "deps with spaces/libhelper.rmeta";
    rustc().input("helper.rs").crate_type("lib").emit("metadata").output(binary).run();
    rfs::copy(binary, "libhelper.rmeta");
    #[cfg(unix)]
    escaped_decoy(binary);

    let plain = compile("plain.d", "libhelper.rmeta");
    let spaced = compile("spaced.d", binary);
    let expected = checksum(&plain, "plain.txt");
    assert!(expected.contains(&format!("file_len:{}", contents.len())));
    for path in paths.iter().copied().chain([visualizer]) {
        assert_eq!(checksum(&plain, path), expected, "plain external dependency: {path}");
        assert_eq!(checksum(&spaced, path), expected, "spaced external dependency: {path}");
    }
    // Trust: explicit --extern paths are canonicalized by the crate locator.
    let plain_binary = std::fs::canonicalize("libhelper.rmeta").unwrap();
    let spaced_binary = std::fs::canonicalize(binary).unwrap();
    assert_eq!(
        checksum(&plain, &plain_binary.to_string_lossy()),
        checksum(&spaced, &spaced_binary.to_string_lossy())
    );

    // Trust: rlib inputs use a separate binary-dependency branch from rmeta inputs.
    let binary = "deps with spaces/libhelper.rlib";
    rustc().input("helper.rs").crate_type("rlib").output("libhelper.rlib").run();
    rfs::copy("libhelper.rlib", binary);
    #[cfg(unix)]
    escaped_decoy(binary);
    let plain = compile("plain-rlib.d", "libhelper.rlib");
    let spaced = compile("spaced-rlib.d", binary);
    let plain_binary = std::fs::canonicalize("libhelper.rlib").unwrap();
    let spaced_binary = std::fs::canonicalize(binary).unwrap();
    assert_eq!(
        checksum(&plain, &plain_binary.to_string_lossy()),
        checksum(&spaced, &spaced_binary.to_string_lossy())
    );
}
