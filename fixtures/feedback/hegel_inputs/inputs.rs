struct Input;

// tc.draw(generators::default::<Input>()); tc.assume(false);
const EXAMPLE: &str = "generators::integers::<u8>().filter(|value| *value > 0)";

#[hegel::test]
fn scattered_draws_are_execution_level(tc: TestCase) {
    let first = tc.draw(generators::default::<Input>());
    let second = tc.draw(generators::default::<Input>());
    consume(first, second);
}

#[hegel::test]
fn destructured_input_controls_if(tc: TestCase) {
    let (input, other) = tc.draw(generators::default::<(Input, Input)>());
    if input.is_valid() {
        consume(other);
    }
}

#[hegel::test]
fn direct_boolean_draw_controls_if(tc: TestCase) {
    if tc.draw(generators::booleans()) {
        consume(Input);
    }
}

#[hegel::test]
fn shadowed_input_is_not_reported(tc: TestCase) {
    let input = tc.draw(generators::default::<Input>());
    {
        let input = false;
        if input {
            consume(Input);
        }
    }
}

#[hegel::test]
fn loop_shadowed_input_is_not_reported(tc: TestCase) {
    let input = tc.draw(generators::default::<Input>());
    for input in [false] {
        if input {
            consume(Input);
        }
    }
}

#[hegel::test]
fn if_let_shadowed_input_is_not_reported(tc: TestCase) {
    let input = tc.draw(generators::default::<Input>());
    if let Some(input) = Some(false) {
        if input {
            consume(Input);
        }
    }
}

#[hegel::test]
fn loop_binding_then_fresh_draw_is_reported(tc: TestCase) {
    let input = tc.draw(generators::default::<Input>());
    for input in [false] {
        let input = tc.draw(generators::default::<Input>());
        if input {
            consume(input);
        }
    }
}

#[hegel::test]
fn assume_filters_a_case(tc: TestCase) {
    let input = tc.draw(generators::default::<Input>());
    tc.assume(input.is_valid());
    consume(input);
}

#[hegel::test]
fn match_shadowed_case_is_not_reported(tc: TestCase) {
    let input = tc.draw(generators::default::<Input>());
    match Some(input) {
        Some(tc) => tc.assume(true),
        None => consume(Input),
    }
}

#[hegel::test]
fn if_let_shadowed_case_is_not_reported(tc: TestCase) {
    let input = tc.draw(generators::default::<Input>());
    if let Some(tc) = Some(Input) {
        tc.assume(true);
    }
}

fn generator_filter() {
    let _ = generators::integers::<u8>().filter(|value| *value > 0);
    let values = [1, 2, 3];
    let _ = values.iter().filter(|value| **value > 0);
}

impl Operation {
    fn apply(&self, tc: &TestCase) {
        let input = tc.draw(generators::default::<Input>());
        consume(input);
    }

    fn after(&self, tc: &TestCase) {
        consume(tc);
    }

    fn resolve_target(&self, rng: &mut Rng) {
        let _ = rng.gen_range(0..4);
    }

    fn resolve_canvas(&self) {
        let _ = paint::draw(Input);
    }

    fn default_generator(tc: &TestCase) {
        let _ = tc.draw(generators::default::<Input>());
    }
}

struct PlainOperation;

impl PlainOperation {
    fn resolve_target(&self, rng: &mut Rng) {
        let _ = rng.gen_range(0..4);
    }
}

#[hegel::state_machine]
impl Machine {
    #[rule]
    fn apply(&self, tc: &TestCase) {
        let _ = tc.draw(generators::default::<Input>());
    }
}

#[hegel::test]
fn generator_compose_draws_are_not_execution_draws(tc: TestCase) {
    let input = tc.draw(hegel::compose!(|inner| {
        let _ = inner.draw(generators::default::<Input>());
        Input
    }));
    consume(input);
}

// shapelint: allow(hegel-input-branch)
#[hegel::test]
fn suppressed_branch(tc: TestCase) {
    let input = tc.draw(generators::default::<Input>());
    if input.is_valid() {
        consume(input);
    }
}

fn consume<T>(_: T) {}

trait InputExt {
    fn is_valid(&self) -> bool;
}

impl InputExt for Input {
    fn is_valid(&self) -> bool {
        true
    }
}

struct Machine;
#[derive(hegel::DefaultGenerator)]
struct Operation;
struct Rng;

impl Rng {
    fn gen_range(&mut self, _: std::ops::Range<u8>) -> u8 {
        0
    }
}
