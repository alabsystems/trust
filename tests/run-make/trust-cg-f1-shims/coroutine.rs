// An `async fn`'s future dropped: coroutine drop glue (refused by shape on the glue lane).
pub async fn f(x: u64) -> u64 {
    x ^ 1
}

pub fn make_and_drop(x: u64) {
    let fut = f(x);
    drop(fut);
}
