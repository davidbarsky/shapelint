/// The single candidate within `min(len / 3, 3)` Damerau-Levenshtein edits of `name`,
/// or `None` when there is no such candidate or more than one.
pub(crate) fn suggest<'a>(
    name: &str,
    candidates: impl IntoIterator<Item = &'a str>,
) -> Option<&'a str> {
    let limit = (name.chars().count() / 3).min(3);
    if limit == 0 {
        return None;
    }
    let mut close = candidates
        .into_iter()
        .filter(|c| *c != name && strsim::damerau_levenshtein(name, c) <= limit);
    let first = close.next()?;
    match close.next() {
        None => Some(first),
        Some(_) => None,
    }
}

/// Wraps a code fragment so it displays in backticks.
pub(crate) struct Code<T>(pub T);

impl<T: std::fmt::Display> std::fmt::Display for Code<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "`{}`", self.0)
    }
}
