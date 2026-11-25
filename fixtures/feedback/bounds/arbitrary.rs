fn bounds(input: &str, generator: &Generator) {
    input.truncate(128);
    input.truncate(12usize);
    let _ = input.chars().take(16);
    let _ = Vec::with_capacity(64);
    retry(5);
    generator.max(32);
    generator.max_value(48);
    generator.max_size(24);
    if input.len() > 256 {
        return;
    }
    if input.len() + 3 > 10 {
        return;
    }
    if marker == 5 {
        return;
    }
    let _ = std::cmp::max(5, marker);
}

fn named_bounds(input: &str, generator: &Generator) {
    input.truncate(MAX_INPUT);
    let _ = input.chars().take(MAX_TAKE);
    let _ = Vec::with_capacity(0x40);
    if input.len() > MAX_LEN {
        generator.max(MAX_GENERATED);
    }
}
