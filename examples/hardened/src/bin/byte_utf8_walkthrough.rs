#[cfg(unix)]
use std::ffi::OsStr;
#[cfg(unix)]
use std::fs;
#[cfg(unix)]
use std::io;
#[cfg(unix)]
use std::os::unix::ffi::OsStrExt;
#[cfg(unix)]
use std::path::PathBuf;

#[cfg(unix)]
use hardened_regression_fixtures::{ScratchDir, hex_bytes};

#[cfg(unix)]
fn main() -> io::Result<()> {
    let scratch = ScratchDir::new("byte-utf8")?;
    let filename_bytes = b"non_utf8_\xff_name";
    let payload = b"payload:\xf0\x28\x8c\x28\n";
    let filename_probe = match scratch.write_file(OsStr::from_bytes(filename_bytes), payload) {
        Ok(path) => probe_supported_filename(&scratch, path, filename_bytes)?,
        Err(error) if is_unsupported_non_utf8_filename(&error) => {
            let path = scratch.write_file(OsStr::new("payload.bin"), payload)?;
            FilenameProbe::Unsupported { path, error }
        }
        Err(error) => return Err(error),
    };

    if String::from_utf8(filename_bytes.to_vec()).is_ok() {
        return Err(io::Error::new(
            io::ErrorKind::Other,
            "non-UTF-8 filename unexpectedly converted with strict UTF-8",
        ));
    }
    let lossy_payload_had_replacement =
        String::from_utf8_lossy(payload).contains(char::REPLACEMENT_CHARACTER);
    if !lossy_payload_had_replacement {
        return Err(io::Error::new(
            io::ErrorKind::Other,
            "invalid payload unexpectedly converted losslessly through lossy UTF-8",
        ));
    }

    let read_to_string_error = match fs::read_to_string(filename_probe.path()) {
        Ok(_) => {
            return Err(io::Error::new(
                io::ErrorKind::Other,
                "invalid payload unexpectedly read as UTF-8 text",
            ));
        }
        Err(error) => error,
    };

    let payload_roundtrip = fs::read(filename_probe.path())?;
    if payload_roundtrip != payload {
        return Err(io::Error::new(
            io::ErrorKind::Other,
            "payload bytes did not round-trip through the filesystem",
        ));
    }

    println!("walkthrough=byte_utf8");
    println!("scratch={}", scratch.path().display());
    println!("filename_hex={}", hex_bytes(filename_bytes));
    println!("payload_hex={}", hex_bytes(payload));
    println!("lossy_payload_had_replacement=yes");
    match filename_probe {
        FilenameProbe::Supported { lossy_had_replacement, .. } => {
            println!("filename_creation=supported");
            println!("path_to_str=none");
            println!(
                "lossy_filename_had_replacement={}",
                if lossy_had_replacement { "yes" } else { "no" }
            );
            println!("roundtrip_filename_bytes=ok");
        }
        FilenameProbe::Unsupported { error, .. } => {
            println!("filename_creation=unsupported");
            println!("filename_create_error={:?}", error.kind());
            println!(
                "filename_create_raw_os_error={}",
                error.raw_os_error().map_or_else(|| "none".to_owned(), |code| code.to_string())
            );
            println!("path_to_str=skipped");
            println!("lossy_filename_had_replacement=skipped");
            println!("roundtrip_filename_bytes=skipped");
        }
    }
    println!("strict_filename_utf8=error");
    println!("read_to_string_error={:?}", read_to_string_error.kind());
    println!("roundtrip_payload_bytes=ok");
    println!("result=non-utf8-demonstrated");

    Ok(())
}

#[cfg(unix)]
enum FilenameProbe {
    Supported { path: PathBuf, lossy_had_replacement: bool },
    Unsupported { path: PathBuf, error: io::Error },
}

#[cfg(unix)]
impl FilenameProbe {
    fn path(&self) -> &std::path::Path {
        match self {
            Self::Supported { path, .. } | Self::Unsupported { path, .. } => path,
        }
    }
}

#[cfg(unix)]
fn probe_supported_filename(
    scratch: &ScratchDir,
    path: PathBuf,
    filename_bytes: &[u8],
) -> io::Result<FilenameProbe> {
    let mut entries = fs::read_dir(scratch.path())?;
    let entry = entries
        .next()
        .transpose()?
        .ok_or_else(|| io::Error::new(io::ErrorKind::NotFound, "scratch file was not created"))?;
    if entries.next().transpose()?.is_some() {
        return Err(io::Error::new(
            io::ErrorKind::Other,
            "scratch directory contained more than the walkthrough file",
        ));
    }

    let roundtrip_name = entry.file_name();
    if roundtrip_name.as_bytes() != filename_bytes {
        return Err(io::Error::new(
            io::ErrorKind::Other,
            "directory entry did not round-trip the non-UTF-8 filename bytes",
        ));
    }

    if path.to_str().is_some() {
        return Err(io::Error::new(
            io::ErrorKind::Other,
            "non-UTF-8 path unexpectedly converted to str",
        ));
    }

    let lossy_name = roundtrip_name.to_string_lossy();
    Ok(FilenameProbe::Supported {
        path,
        lossy_had_replacement: lossy_name.contains(char::REPLACEMENT_CHARACTER),
    })
}

#[cfg(unix)]
fn is_unsupported_non_utf8_filename(error: &io::Error) -> bool {
    matches!(error.kind(), io::ErrorKind::InvalidInput | io::ErrorKind::InvalidData)
        || matches!(error.raw_os_error(), Some(84 | 92))
}

#[cfg(not(unix))]
fn main() {
    println!("walkthrough=byte_utf8");
    println!("unsupported=non-unix");
}
