pub trait Clock {
    fn run(&self);
}

struct Worker;

impl crate /* trivia */ :: Clock for Worker {
    fn run(&self) {}
}
