pub struct SystemClock;

impl Clock for SystemClock {
    fn now(&self) -> u64 { 0 }
}
