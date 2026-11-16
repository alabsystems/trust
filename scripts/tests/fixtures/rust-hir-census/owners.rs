//! HIR inventory control: none of these bodies may depend on producer admission.
mod auxiliary;

pub const NAMED: u32 = 3;
pub static STORED: u32 = 4;

pub fn nested(value: u32) -> u32 {
    const LOCAL: u32 = 5;
    let closure = |argument: u32| argument + LOCAL;
    closure(value) + const { 6 } + auxiliary::value()
}

pub async fn coroutine(value: u32) -> u32 {
    async move { value + NAMED }.await
}

pub async fn generated_by_move() -> usize {
    async fn invoke<F: AsyncFnOnce() -> usize>(function: F) -> usize {
        function().await
    }
    let owned = String::from("census");
    let closure = async || owned.len();
    invoke(closure).await
}

pub fn λ(value: u32) -> u32 {
    value
}
