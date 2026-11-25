#[test]
fn fixed_cases_are_one_test() {
    for (input, expected) in [("a", "A"), ("b", "B")] {
        assert_eq!(normalize(input), expected);
    }
}

#[test]
fn named_cases_are_one_test() {
    let cases = [("a", "A"), ("b", "B")];
    for case in cases {
        assert_eq!(normalize(case.0), case.1);
    }
}

#[test]
fn borrowed_named_cases_are_one_test() {
    let cases = [("a", "A"), ("b", "B")];
    for case in &cases {
        assert_eq!(normalize(case.0), case.1);
    }
}

#[test]
fn vec_named_cases_are_one_test() {
    let cases = vec![("a", "A"), ("b", "B")];
    for case in cases {
        assert_eq!(normalize(case.0), case.1);
    }
}

#[test]
fn state_words_inside_strings_are_cases() {
    for case in ["state.step(", "history"] {
        let text = case;
        assert_eq!(text.len() > 0, true);
    }
}

#[test]
fn history_is_one_case() {
    for step in history {
        let action = tc.draw(0..=3);
        state.apply(step, action);
    }
}

#[test]
fn state_machine_history_is_one_case() {
    for event in [Open, Close] {
        state.step(event);
        assert_eq!(state.current(), event);
    }
}

#[test]
fn typed_action_is_not_primitive() {
    let action = tc.draw(any::<Action>());
    assert!(action.is_valid());
}

#[test]
fn primitive_draw_maps_actions() {
    let action = match tc.draw(0..=3) {
        0 => Action::Put,
        1 => Action::Delete,
        _ => Action::Read,
    };
    assert!(action.is_valid());
}

#[test]
fn generator_draw_maps_actions() {
    let action = tc.draw(generators::integers::<u8>().max_value(2));
    match action {
        0 => assert_eq!(state.current(), Open),
        _ => assert_eq!(state.current(), Close),
    }
}

#[test]
fn numeric_generator_inside_match_arm_is_data() {
    match state.current() {
        Open => {
            let value = tc.draw(generators::integers::<u8>().max_value(2));
            assert!(value < 3);
        }
        Close => {}
    }
}

#[hegeltest::test(test_cases = 12)]
fn local_budget_is_reported() {}

#[hegel::test(test_cases = 8)]
fn generated_typed_case_is_not_primitive() {
    let action = tc.draw(any::<Action>());
    assert!(action.is_valid());
}

#[some_other::test(test_cases = 12)]
fn other_budget_is_not_reported() {}

#[hegel::test(note = "test_cases = 1")]
fn budget_text_is_not_reported() {}

#[hegel::test(note(test_cases = 1))]
fn nested_budget_is_not_reported() {}

#[hegel::test]
fn uncapped_primitive_choice(tc: TestCase) {
    match tc.draw(generators::integers::<u8>()) {
        0 => execute(Action::Insert),
        1 => execute(Action::Delete),
        _ => execute(Action::Read),
    }
}

#[test]
fn shadowed_dynamic_cases_are_not_a_fixed_array() {
    let cases = [1, 2];
    {
        let cases = load_cases();
        for case in cases { assert!(check(case)); }
    }
}
