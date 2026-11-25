#[hegel::test]
fn profile_controls_settings() {
    let text = "#[hegel::test(seed = 7)]";
    let history = load_history();
    for action in history {
        match apply(action) {
            Ok(()) => record(action),
            Err(error) => record(error),
        }
    }
}

#[hegel::test]
fn exits_in_else_and_unrelated_branches_are_ignored() {
    for action in history {
        if let Err(error) = apply(action) {
            record(error);
        } else {
            break;
        }
        if ready(action) {
            if let Err(error) = inspect(action) {
                record(error);
            }
            break;
        }
    }
}

#[hegel::test]
fn inner_break_only_exits_nested_loop() {
    for action in actions {
        loop {
            match operation() {
                Err(_) => break,
                Ok(_) => {}
            }
        }
        observe(action);
    }
}

#[hegel::test]
fn nested_functions_and_closures_are_ignored() {
    fn nested() {
        for action in history {
            match apply(action) {
                Ok(()) => record(action),
                Err(_) => break,
            }
        }
    }
    for action in history {
        let check = || {
            if let Err(error) = inspect(action) {
                record(error);
                return;
            }
        };
        check();
    }
}

#[hegel::test]
fn error_arm_outside_history_loop_is_ignored() {
    match request() {
        Err(_) => {
            for action in history {
                break;
            }
        }
        Ok(_) => {}
    }
}

#[hegel::test(suppress_health_check = [])]
fn disabled_settings_are_not_fixed() {}

#[some_other::test(seed = 11, derandomize = true, suppress_health_check = [TooSlow])]
fn unrelated_test_attribute_is_ignored() {}

#[hegel::state_machine]
impl ModelWithoutOverrides {
    #[rule]
    fn action(&mut self, tc: TestCase) {}

    #[invariant(always_run)]
    fn state_is_safe(&self) {}
}
