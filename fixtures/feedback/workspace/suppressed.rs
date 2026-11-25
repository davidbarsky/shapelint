// shapelint: allow(single-impl-trait)
pub trait Suppressed {
    fn run(&self);
}

impl Suppressed for Worker {
    fn run(&self) {}
}

struct Worker;
