use std::io;
use std::path::Path;

pub(crate) fn byte_exact_boundary(path: &Path, bytes: &[u8]) -> io::Result<String> {
    let _text = std::fs::read_to_string(path)?;
    let _lossy_stream = String::from_utf8_lossy(bytes);
    let _lossy_path = path.as_os_str().to_string_lossy();
    let _strict_slice = std::str::from_utf8(bytes)
        .map_err(|error| io::Error::new(io::ErrorKind::InvalidData, error))?;
    let strict = String::from_utf8(bytes.to_vec())
        .map_err(|error| io::Error::new(io::ErrorKind::InvalidData, error))?;
    let _path_text = path.to_str().unwrap();
    Ok(strict)
}
