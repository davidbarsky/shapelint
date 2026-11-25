pub enum Step {
    Stop,
    Again,
}

fn value(step: Step) -> u32 {
    match step {
        Step::Stop => 1,
        Step::Again => value(Step::Stop),
    }
}

pub fn established() -> u32 {
    value(Step::Again) - 1
}

pub fn contradicted() -> u32 {
    value(Step::Again) - 2
}
