use std::future::Future;
use std::pin::Pin;

pub enum Step {
    Done(u32),
    Pending(u32),
}

pub async fn complete(
    operation: fn() -> Result<Step, u8>,
    wait: fn(u32) -> Pin<Box<dyn Future<Output = Result<(), u8>>>>,
) -> Result<u32, u8> {
    loop {
        match operation()? {
            Step::Done(value) => return Ok(value),
            Step::Pending(completions) => {
                let guard = String::from("pending");
                wait(completions).await?;
                drop(guard);
            }
        }
    }
}
