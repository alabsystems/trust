// Dev helper: `cargo run --example transform_file -- path.ts` prints the
// transform outcome (enum/namespace lowering + type erasure). Not shipped.
use std::io::Read;

fn main() {
    let path = std::env::args().nth(1).expect("usage: transform_file <path.ts>");
    let mut s = String::new();
    std::fs::File::open(&path).expect("open").read_to_string(&mut s).expect("read");
    match trust_ts_strip::transform(&s) {
        trust_ts_strip::StripOutcome::Js(js) => {
            print!("{js}");
        }
        trust_ts_strip::StripOutcome::Refused(r) => {
            eprintln!("REFUSED: {r}");
            std::process::exit(3);
        }
    }
}
