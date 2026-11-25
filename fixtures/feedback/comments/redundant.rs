// TODO: move this test to the shared suite
// ---------------- test helpers ----------------
// fixed_cases
fn fixed_cases() {}

// Keep this because it records why this boundary is required.
fn required_boundary() {}

fn string_literals_are_not_comments() {
    let text = "TODO: this is data, not a comment";
    let _ = text;
}

// use example::Thing as Alias;
const IMPORT_LIKE_TEXT: &str = "use example::Thing as Alias;";

/// documented
fn documented() {}
