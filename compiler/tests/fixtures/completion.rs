pub enum Step {
    Done(u32),
    Pending(u32),
}

// shapelint: allow(shallow-helper) Identical bodies isolate resolved callee identity in the test.
pub fn observe(step: Step) -> Step {
    step
}

// shapelint: allow(shallow-helper) Identical bodies isolate resolved callee identity in the test.
pub fn observe_other(step: Step) -> Step {
    step
}

pub fn complete(
    operation: fn() -> Result<Step, u8>,
    wait: fn(u32) -> Result<(), u8>,
) -> Result<u32, u8> {
    loop {
        match observe(operation()?) {
            Step::Done(value) => return Ok(value),
            Step::Pending(completions) => wait(completions)?,
        }
    }
}
