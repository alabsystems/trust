//! Live compiler negative controls. Every generated body remains in the
//! inventory, but no function may be invented for unmodeled effects or types.
async fn consume<F: AsyncFnOnce() -> u32>(function: F) -> u32 { function().await }

pub async fn real_call(value: u32) -> u32 {
    let closure = async move || value.wrapping_add(1);
    consume(closure).await
}

pub async fn borrowed_capture(value: &u32) -> u32 {
    let closure = async move || *value;
    consume(closure).await
}

pub async fn real_suspend(value: u32) -> u32 {
    let closure = async move || { async {}.await; value };
    consume(closure).await
}
