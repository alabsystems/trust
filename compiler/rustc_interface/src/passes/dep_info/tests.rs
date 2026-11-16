use rustc_span::SourceFileHashAlgorithm;

use super::*;

fn prepared() -> PreparedDepInfo {
    let mut files = IndexMap::default();
    files.insert(
        escape_dep_filename("src/a b.rs"),
        (3, Some(SourceFileHash::new_in_memory(SourceFileHashAlgorithm::Sha256, b"abc"))),
    );
    files.insert(escape_dep_filename("plain.rs"), (0, None));
    PreparedDepInfo::new(
        OutFileName::Stdout,
        vec!["out one".into(), "out/two".into()],
        files,
        vec![
            (escape_dep_env("Z"), Some(escape_dep_env("line\ncar\r\\slash"))),
            (escape_dep_env("A"), None),
        ],
        Some(7),
        true,
    )
}

#[test]
fn canonical_bytes_preserve_order_escaping_witness_environment_and_checksums() {
    let mut bytes = Vec::new();
    prepared().write_buffered(BufWriter::new(&mut bytes)).unwrap();
    assert_eq!(
        bytes,
        concat!(
            "out one: src/a\\ b.rs plain.rs\n\n",
            "out/two: src/a\\ b.rs plain.rs\n\n",
            "src/a\\ b.rs:\n",
            "plain.rs:\n",
            "# trust-witness-output-v1:0000000000000007.twit\n",
            "\n",
            "# env-dep:A\n",
            "# env-dep:Z=line\\ncar\\r\\\\slash\n",
            "# checksum:sha256=ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad file_len:3 src/a\\ b.rs\n",
        )
        .as_bytes(),
    );
}

#[test]
fn empty_inventory_and_checksum_switch_keep_the_existing_format() {
    let empty = PreparedDepInfo::new(
        OutFileName::Stdout,
        vec!["out".into()],
        IndexMap::default(),
        Vec::new(),
        None,
        true,
    );
    let mut bytes = Vec::new();
    empty.write_buffered(BufWriter::new(&mut bytes)).unwrap();
    assert_eq!(bytes, b"out: \n\n");

    let mut without_checksums = prepared();
    without_checksums.emit_checksums = false;
    bytes.clear();
    without_checksums.write_buffered(BufWriter::new(&mut bytes)).unwrap();
    assert!(!String::from_utf8(bytes).unwrap().contains("# checksum:"));
}

#[test]
fn escaping_is_exact_and_the_prepared_carrier_is_owned() {
    fn owned<T: 'static>() {}
    owned::<PreparedDepInfo>();
    assert_eq!(escape_dep_filename("space here\\#$"), "space\\ here\\#$");
    assert_eq!(escape_dep_filename(String::from("plain")), "plain");
    assert_eq!(escape_dep_env("λ =#\n\r\\"), "λ =#\\n\\r\\\\");
    assert_eq!(escape_dep_env("plain =#λ"), "plain =#λ");
}

#[test]
fn terminal_tool_inputs_are_one_marker_after_the_canonical_body() {
    // Obtain terminal bytes from the shared codec rather than maintaining
    // a second JSON formatter in the compiler or this control.
    let bytes = trust_fs_observation::tool_lookup::ToolInputs::from_records(Vec::new())
        .unwrap()
        .encode()
        .unwrap();
    let mut prepared = prepared();
    let mut original = Vec::new();
    prepared.write_body(&mut original).unwrap();
    prepared.set_tool_inputs(Some(Terminal::Available(bytes.clone())));
    let mut actual = Vec::new();
    prepared.write_buffered(BufWriter::new(&mut actual)).unwrap();
    let mut expected = original.clone();
    expected.extend_from_slice(DEP_INFO_PREFIX.as_bytes());
    expected.extend_from_slice(&bytes);
    expected.push(b'\n');
    assert_eq!(actual, expected);

    prepared.set_tool_inputs(Some(Terminal::Unavailable));
    actual.clear();
    prepared.write_buffered(BufWriter::new(&mut actual)).unwrap();
    original.extend_from_slice(format!("{DEP_INFO_PREFIX}{UNAVAILABLE}\n").as_bytes());
    assert_eq!(actual, original);
    assert_eq!(String::from_utf8(actual).unwrap().matches(DEP_INFO_PREFIX).count(), 1);
}

struct FailedWriter {
    bytes: Vec<u8>,
    fail_write: bool,
    flushes: usize,
}

impl Write for FailedWriter {
    fn write(&mut self, bytes: &[u8]) -> io::Result<usize> {
        if self.fail_write {
            return Err(io::Error::new(io::ErrorKind::BrokenPipe, "write failure"));
        }
        self.bytes.extend_from_slice(bytes);
        Ok(bytes.len())
    }

    fn flush(&mut self) -> io::Result<()> {
        self.flushes += 1;
        Err(io::Error::new(io::ErrorKind::BrokenPipe, "final flush failure"))
    }
}

#[test]
fn body_write_failure_is_returned_before_successful_emission() {
    let mut prepared = prepared();
    prepared.output_paths = vec!["x".repeat(32 * 1024).into()];
    let mut file = FailedWriter { bytes: Vec::new(), fail_write: true, flushes: 0 };
    let error = prepared.write_buffered(BufWriter::new(&mut file)).unwrap_err();
    assert_eq!(error.kind(), io::ErrorKind::BrokenPipe);
    assert_eq!(error.to_string(), "write failure");
    assert_eq!(file.flushes, 0);
}

#[test]
fn final_buffer_drain_failure_is_not_discarded_by_drop() {
    let prepared = prepared();
    let mut expected = Vec::new();
    prepared.write_body(&mut expected).unwrap();
    assert!(expected.len() < BufWriter::new(io::sink()).capacity());
    let mut file = FailedWriter { bytes: Vec::new(), fail_write: true, flushes: 0 };
    // Every body write fits in the buffer, so the underlying write fails
    // only at the final drain. Relying on BufWriter::drop would return Ok.
    let error = prepared.write_buffered(BufWriter::new(&mut file)).unwrap_err();
    assert_eq!(error.kind(), io::ErrorKind::BrokenPipe);
    assert_eq!(error.to_string(), "write failure");
    assert!(file.bytes.is_empty());
    assert_eq!(file.flushes, 0);
}

#[test]
fn final_buffered_flush_failure_is_returned_after_body_was_written() {
    let mut file = FailedWriter { bytes: Vec::new(), fail_write: false, flushes: 0 };
    let error = prepared().write_buffered(BufWriter::new(&mut file)).unwrap_err();
    assert_eq!(error.kind(), io::ErrorKind::BrokenPipe);
    assert_eq!(error.to_string(), "final flush failure");
    assert!(file.bytes.starts_with(b"out one:"));
    assert_eq!(file.flushes, 1);
}
