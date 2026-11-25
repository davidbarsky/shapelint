use std::sync::Arc;

/// A byte range in the source. Offsets fit in `u32` because [`SourceInput`] is size-checked.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, serde::Serialize)]
pub struct Span {
    pub start: u32,
    pub end: u32,
}

impl From<Span> for std::ops::Range<usize> {
    fn from(span: Span) -> std::ops::Range<usize> {
        span.start as usize..span.end as usize
    }
}

/// Holds source text whose byte offsets fit in `u32`.
#[derive(Clone, Debug, serde::Serialize)]
pub struct SourceInput {
    pub name: Arc<str>,
    pub(crate) text: Arc<SourceText>,
}

/// Why a source could not be linted.
#[derive(Debug, thiserror::Error)]
pub enum LintError {
    #[error("compiler source text is unavailable for {name}")]
    Unavailable { name: String },
    #[error("invalid source span {span:?} in {name}")]
    InvalidSpan { name: String, span: crate::Span },
    #[error("could not parse Rust source {name}")]
    Parse { name: String },
    #[error(
        "{name} is {len} bytes; shapelint handles sources up to {} bytes",
        u32::MAX
    )]
    TooLarge { name: String, len: usize },
    /// The parser recurses once per nesting level, so each source gets a thread whose stack
    /// is sized from its token count; this is the OS refusing that thread.
    #[error("could not start a parser thread with a {stack_bytes}-byte stack for {name}: {source}")]
    NoStack {
        name: String,
        stack_bytes: usize,
        source: std::io::Error,
    },
}

impl TryFrom<&rustc_span::SourceFile> for SourceInput {
    type Error = LintError;

    fn try_from(file: &rustc_span::SourceFile) -> Result<Self, Self::Error> {
        let name = file.name.prefer_local_unconditionally().to_string();
        let external = file.external_src.read();
        let text = match &file.src {
            Some(text) => text.as_str(),
            None => match external.get_source() {
                Some(text) => text,
                None => return Err(LintError::Unavailable { name }),
            },
        };
        let mut original = String::new();
        // Normalized positions follow removed CRLF pairs; position zero marks a leading BOM.
        let mut positions = file.normalized_pos.iter().peekable();
        if let Some(_) = positions.next_if(|position| position.pos.0 == 0) {
            original.push('\u{feff}');
        }
        for (offset, character) in text.char_indices() {
            if let Some(_) = positions
                .next_if(|position| position.pos.0 as usize == offset + character.len_utf8())
            {
                original.push('\r');
            }
            original.push(character);
        }
        Self::try_new(name, original)
    }
}

impl SourceInput {
    pub fn try_new(
        name: impl Into<String>,
        text: impl Into<String>,
    ) -> Result<SourceInput, LintError> {
        let name = name.into();
        let text = text.into();
        let len = text.len();
        if len > u32::MAX as usize {
            return Err(LintError::TooLarge { name, len });
        }
        let input = SourceInput {
            name: name.into(),
            text: Arc::new(SourceText::new(text)),
        };
        Ok(input)
    }

    pub(crate) fn window(&self, span: Span) -> Result<Window<'_>, LintError> {
        let text = self.as_ref();
        let (first, bytes) = self.text.lines_covering(span);
        let offset = bytes.start;
        let text = text.get(bytes).ok_or_else(|| LintError::InvalidSpan {
            name: self.name.to_string(),
            span,
        })?;
        Ok(Window {
            name: &self.name,
            text,
            offset,
            line: first,
        })
    }
}

pub(crate) struct Window<'a> {
    name: &'a str,
    pub(crate) text: &'a str,
    offset: usize,
    pub(crate) line: usize,
}

impl Window<'_> {
    pub(crate) fn relative(&self, span: Span) -> Result<std::ops::Range<usize>, LintError> {
        let invalid = || LintError::InvalidSpan {
            name: self.name.to_owned(),
            span,
        };
        let start = (span.start as usize)
            .checked_sub(self.offset)
            .ok_or_else(invalid)?;
        let end = (span.end as usize)
            .checked_sub(self.offset)
            .ok_or_else(invalid)?;
        let range = start..end;
        self.text.get(range.clone()).ok_or_else(invalid)?;
        Ok(range)
    }
}

/// Shares immutable source text and the line indexes derived from it.
#[derive(Debug, serde::Serialize)]
#[serde(transparent)]
pub(crate) struct SourceText {
    text: String,
    #[serde(skip)]
    starts: Vec<u32>,
    #[serde(skip)]
    comment_lines: Vec<Option<()>>,
}

#[derive(Debug, PartialEq, Eq)]
pub(crate) struct Position {
    pub line: usize,
    pub col: usize,
}

impl SourceText {
    fn new(text: String) -> Self {
        let starts = std::iter::once(0)
            .chain(text.match_indices('\n').map(|(at, _)| (at + 1) as u32))
            .collect();
        let comment_lines = text
            .lines()
            .map(|line| line.contains("//").then_some(()))
            .collect();
        SourceText {
            text,
            starts,
            comment_lines,
        }
    }

    fn lines_covering(&self, span: Span) -> (usize, std::ops::Range<usize>) {
        // A trailing newline does not create another line in annotate-snippets.
        let begins_before = |start: u32, position: u32| {
            start == 0 || (start <= position && (start as usize) < self.text.len())
        };
        let first = self
            .starts
            .partition_point(|&start| begins_before(start, span.start));
        let last = self
            .starts
            .partition_point(|&start| begins_before(start, span.end));
        let offset = self.start_before(first) as usize;
        let end = self
            .starts
            .get(last)
            .map_or(self.text.len(), |&byte| byte as usize);
        (first, offset..end)
    }

    pub(crate) fn line_col(&self, offset: u32) -> Position {
        let before = self.starts.partition_point(|&start| start <= offset);
        let start = self.start_before(before);
        Position {
            line: before,
            col: (start as usize..=offset as usize).count(),
        }
    }

    fn start_before(&self, end: usize) -> u32 {
        let (lines, _) = self.starts.split_at(end);
        *lines
            .last()
            .expect("every source starts with line one at byte zero")
    }

    // Lexer offsets advance monotonically through this source.
    pub(crate) fn line_cursor(&self) -> impl FnMut(u32) -> usize + '_ {
        let mut starts = (1usize..).zip(self.starts.iter().copied()).peekable();
        let mut current = 1;
        move |offset| {
            while let Some((number, _)) = starts.next_if(|&(_, start)| start <= offset) {
                current = number;
            }
            current
        }
    }

    pub(crate) fn nearby_comment(&self, offset: u32, preceding: usize) -> Option<usize> {
        let line = self.line_col(offset).line;
        let start = line.saturating_sub(preceding).saturating_sub(1);
        let end = (line + 1).min(self.comment_lines.len());
        self.comment_lines[start..end]
            .iter()
            .enumerate()
            .find_map(|(index, has_comment)| has_comment.map(|()| index + start))
    }
}

impl AsRef<str> for SourceInput {
    fn as_ref(&self) -> &str {
        &self.text.text
    }
}
