#[hegel::test(seed = 42, suppress_health_check = [HealthCheck::TooSlow])]
fn fixed_seed_and_health_check_are_reviewed() {
    let history = [Open, Close];
    for action in history {
        match apply(action) {
            Ok(()) => record(action),
            Err(_) => break,
        }
    }
}

#[hegel::test(derandomize = true)]
fn derived_seed_is_reviewed() {}

#[hegel::test(derandomize = false)]
fn explicit_derandomization_policy_is_reviewed() {}

#[hegel::test]
fn if_let_error_stops_action_history() {
    for operation in operations {
        if let Err(error) = apply(operation) {
            record(error);
            return;
        }
    }
}

#[hegel::test]
fn labeled_history_exit_stops_action_history() {
    'history: for action in actions {
        loop {
            match operation() {
                Err(_) => break 'history,
                Ok(_) => {}
            }
        }
        observe(action);
    }
}

#[hegel::state_machine]
impl Model {
    #[rule(weight = 2.0)]
    fn action(&mut self, tc: TestCase) {}

    #[invariant]
    fn state_is_safe(&self) {}

    #[invariant(always_run)]
    fn state_is_always_safe(&self) {}
}
