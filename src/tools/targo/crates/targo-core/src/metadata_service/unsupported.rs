//! No native controller transport exists for this Unix platform. These entry
//! points refuse before inspecting stdin, SDKs, host stores or resource data.

use std::ffi::OsString;
use std::io;
use trust_resource_controller::METADATA_STARTUP_ARGUMENT;

use crate::util::CargoResult;

fn unavailable() -> io::Error {
    io::Error::new(
        io::ErrorKind::Unsupported,
        "native metadata service is unsupported on this Unix platform",
    )
}

pub fn capabilities() -> &'static str {
    r#"{"version":3,"sealed_metadata":null}"#
}

pub fn requested(args: &[OsString]) -> bool {
    args.first()
        .is_some_and(|arg| arg == METADATA_STARTUP_ARGUMENT)
}

pub fn run(_args: &[OsString]) -> CargoResult<()> {
    Err(unavailable().into())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn unsupported_service_refuses_before_input_or_native_transport_use() {
        assert!(requested(&[METADATA_STARTUP_ARGUMENT.into()]));
        assert!(!requested(&[]));
        assert_eq!(capabilities(), r#"{"version":3,"sealed_metadata":null}"#);
        let error = run(&[METADATA_STARTUP_ARGUMENT.into()]).unwrap_err();
        assert_eq!(
            error.downcast_ref::<io::Error>().unwrap().kind(),
            io::ErrorKind::Unsupported
        );
    }
}
