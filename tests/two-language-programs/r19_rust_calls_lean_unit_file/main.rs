// Rust `main` calls a Clean `def` authored OUT OF LINE in `helper.lean` — the
// spelling Lean itself uses (G2), not the Trust-specific `.clean`.
clean mod helper;
fn main() {
    let g = crate::pick(6u64, 7u64);
    assert_eq!(g, 6);
    println!("pick(6,7) = {g} from helper.lean");
}
