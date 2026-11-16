//! Static trusted-entry diagnostic, without a DSO loader or macro authority.
fn main() {
    trust_worker_linux::native::entry_fixture();
}
