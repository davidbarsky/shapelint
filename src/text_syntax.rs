use crate::{Language, Span};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum TokenKind {
    Word,
    String,
    MultilineString,
    Comment,
    Symbol(char),
}

#[derive(Debug)]
pub(crate) struct Token {
    pub kind: TokenKind,
    pub span: Span,
}

pub(crate) fn lex(text: &str, language: Language) -> Vec<Token> {
    let mut tokens = Vec::new();
    let mut chars = text.char_indices().peekable();
    while let Some((start, ch)) = chars.next() {
        if ch.is_whitespace() {
            continue;
        }
        let kind = match ch {
            '#' => {
                while let Some((_, ch)) = chars.peek()
                    && *ch != '\n'
                {
                    chars.next();
                }
                TokenKind::Comment
            }
            '\'' | '"' => {
                let quote = ch;
                let delimiter = match &text[start..start + 1] {
                    "'" if text[start..].starts_with("'''") => "'''",
                    "\"" if text[start..].starts_with("\"\"\"") => "\"\"\"",
                    single => single,
                };
                for _ in 1..delimiter.len() {
                    chars.next();
                }
                let kind = match delimiter.len() {
                    1 => TokenKind::String,
                    _ => TokenKind::MultilineString,
                };
                while let Some((at, ch)) = chars.next() {
                    if ch == '\\' && (language == Language::Starlark || quote == '"') {
                        chars.next();
                    } else if text[at..].starts_with(delimiter) {
                        for _ in 1..delimiter.len() {
                            chars.next();
                        }
                        // TOML permits one or two extra quotes before the closing triple quote.
                        if language == Language::Toml && kind == TokenKind::MultilineString {
                            while let Some((_, ch)) = chars.peek()
                                && *ch == quote
                            {
                                chars.next();
                            }
                        }
                        break;
                    }
                }
                kind
            }
            ch if ch.is_alphanumeric() || ch == '_' || ch == '-' => {
                while let Some((_, ch)) = chars.peek()
                    && (ch.is_alphanumeric() || ['_', '-', '.'].contains(ch))
                {
                    chars.next();
                }
                TokenKind::Word
            }
            symbol => TokenKind::Symbol(symbol),
        };
        let end = chars.peek().map_or(text.len(), |(at, _)| *at);
        tokens.push(Token {
            kind,
            span: Span {
                start: u32::try_from(start).expect("source was size-checked"),
                end: u32::try_from(end).expect("source was size-checked"),
            },
        });
    }
    tokens
}
