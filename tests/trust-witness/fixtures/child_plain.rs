// A plain inline-const child body with no method/operator pick. The one-body
// checker cannot validate the child's node types, adjustments, field indices,
// signatures, or cast flags, so the containing root must not replay yet.
pub fn f(x: i32) -> i32 {
    x + const {
        let y = 1;
        y
    }
}
