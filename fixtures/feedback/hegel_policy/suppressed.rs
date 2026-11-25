// shapelint: allow(all)
#[hegel::test(seed = 42, suppress_health_check = [HealthCheck::TooSlow])]
fn suppressed_settings() {
    let history = [Open, Close];
    for action in history {
        match apply(action) {
            Ok(()) => record(action),
            Err(_) => break,
        }
    }
}

#[hegel::state_machine]
impl SuppressedModel {
    // shapelint: allow(all)
    #[rule(weight = 2.0)]
    fn action(&mut self, tc: TestCase) {}

    // shapelint: allow(all)
    #[invariant]
    fn state_is_safe(&self) {}
}
