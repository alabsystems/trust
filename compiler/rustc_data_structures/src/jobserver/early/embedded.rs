//! A late embedding must never claim the official raw-slot capture contract.
#[path = "../early.rs"]
mod early;
fn main() {
    let _activity = std::fs::File::open("/dev/null").unwrap();
    if early::local(3, false).is_err() {
        std::process::exit(75);
    }
}
