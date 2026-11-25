pub struct TestClock;

impl Clock for TestClock {
    fn now(&self) -> u64 { 1 }
}
