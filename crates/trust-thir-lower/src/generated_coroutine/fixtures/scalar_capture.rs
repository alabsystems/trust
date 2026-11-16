//! Live compiler control: the AsyncFnOnce call creates a real synthetic by-move
//! body. Its actual built MIR must be inspected; the ordinary async parent is
//! not a substitute for the generated body or its verdict.
async fn consume<F: AsyncFnOnce() -> u32>(function: F) -> u32 { function().await }

pub async fn scalar_capture(value: u32) -> u32 {
    let closure = async move || value;
    consume(closure).await
}
