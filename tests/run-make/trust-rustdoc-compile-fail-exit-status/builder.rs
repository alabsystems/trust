// Trust: an exit-status protocol fixture, not a compiler or proof authority.
fn main() {
    // Consume the source so the parent cannot race a broken stdin pipe.
    let _source = std::io::read_to_string(std::io::stdin()).unwrap();
    let mode = std::env::var("TEST_BUILDER_EXIT").unwrap();
    if mode == "panic" {
        panic!("controlled test-builder panic");
    }
    #[cfg(unix)]
    if mode == "signal" {
        unsafe extern "C" {
            fn raise(signal: i32) -> i32;
        }
        // SAFETY: terminate only this owned protocol-fixture process.
        unsafe { raise(15) };
        panic!("controlled signal did not terminate the fixture");
    }
    let status = mode.parse().unwrap();
    eprintln!("controlled test-builder exit {status}");
    std::process::exit(status);
}
