//! Line-level rules for config and build files (TOML, Buck/Bazel Starlark).

use crate::diagnostic::{Report, Sink};
use crate::suggest::Code;
use crate::text_syntax::{Token, TokenKind};
use crate::{Config, SourceInput, Span};

pub(crate) fn lint_toml(sink: &mut Sink, tokens: &[Token], input: &SourceInput, config: &Config) {
    let text = input.as_ref();
    let min_millis = config.t.duration_comment_min_hours as u128 * 3_600_000;
    let assignments = tokens.windows(3).enumerate();
    for (index, assignment) in assignments {
        let [key, equals, value] = assignment else {
            unreachable!("windows have three tokens")
        };
        if equals.kind != TokenKind::Symbol('=') {
            continue;
        }
        let key_text = match key.kind {
            TokenKind::Word | TokenKind::String => {
                text[std::ops::Range::from(key.span)].trim_matches(['"', '\''])
            }
            TokenKind::MultilineString | TokenKind::Comment | TokenKind::Symbol(_) => continue,
        };
        let value_text = match value.kind {
            TokenKind::Word | TokenKind::String => {
                text[std::ops::Range::from(value.span)].trim_matches(['"', '\''])
            }
            TokenKind::MultilineString | TokenKind::Comment | TokenKind::Symbol(_) => continue,
        };
        let line_start = text[..key.span.start as usize]
            .rfind('\n')
            .map_or(0, |at| at + 1);
        if !text[line_start..key.span.start as usize].trim().is_empty()
            || text[key.span.start as usize..value.span.end as usize].contains('\n')
        {
            continue;
        }
        let line_end = text[value.span.end as usize..]
            .find('\n')
            .map_or(text.len(), |at| value.span.end as usize + at);
        if !text[value.span.end as usize..line_end].trim().is_empty() {
            continue;
        }
        if let Some(previous) = index.checked_sub(1).and_then(|i| tokens.get(i))
            && previous.kind == TokenKind::Comment
            && input.text.line_col(previous.span.start).line + 1
                == input.text.line_col(key.span.start).line
        {
            let comment_start = text[..previous.span.start as usize]
                .rfind('\n')
                .map_or(0, |at| at + 1);
            if text[comment_start..previous.span.start as usize]
                .trim()
                .is_empty()
            {
                continue;
            }
        }
        let lower = key_text.to_ascii_lowercase();
        let Ok(amount) = value_text.replace('_', "").parse::<u128>() else {
            continue;
        };
        let millis = if lower.ends_with("ms") || lower.contains("millis") {
            amount
        } else if lower.ends_with(".s")
            || lower.ends_with("_s")
            || lower.ends_with("secs")
            || lower.ends_with("seconds")
        {
            amount.saturating_mul(1000)
        } else {
            continue;
        };
        if millis < min_millis {
            continue;
        }
        let line_end = line_end - usize::from(text[..line_end].ends_with('\r'));
        let end = u32::try_from(line_end).expect("source was size-checked");
        let human = human_duration(millis);
        let report = Report::new(
            format!(
                "{} is {amount} with no comment giving its unit",
                Code(key_text)
            ),
            value.span,
            human.clone(),
        )
        .suggest(
            "say the duration in human units",
            Span { start: end, end },
            format!(" # {human}"),
        );
        sink.emit(
            "duration-comment",
            Span {
                start: u32::try_from(line_start).expect("source was size-checked"),
                end,
            },
            key_text,
            report,
        );
    }
}

pub(crate) fn lint_starlark(sink: &mut Sink, tokens: &[Token], text: &str) {
    let assignments = tokens.windows(2).enumerate();
    for (index, assignment) in assignments {
        let [name, equals] = assignment else {
            unreachable!("windows have two tokens")
        };
        if name.kind != TokenKind::Word
            || &text[std::ops::Range::from(name.span)] != "mapped_srcs"
            || equals.kind != TokenKind::Symbol('=')
        {
            continue;
        }
        if let Some(next) = tokens.get(index + 2)
            && next.kind == TokenKind::Symbol('=')
        {
            continue;
        }
        let start = text[..name.span.start as usize]
            .rfind('\n')
            .map_or(0, |at| at + 1);
        let end = text[name.span.end as usize..]
            .find('\n')
            .map_or(text.len(), |at| name.span.end as usize + at);
        let end = end - usize::from(text[..end].ends_with('\r'));
        let report = Report::new(
            "`mapped_srcs` remaps the source tree",
            name.span,
            "remapped here",
        )
        .help("keep the standard layout and declare generated inputs explicitly");
        sink.emit(
            "mapped-srcs",
            Span {
                start: u32::try_from(start).expect("source was size-checked"),
                end: u32::try_from(end).expect("source was size-checked"),
            },
            "mapped_srcs",
            report,
        );
    }
}

fn human_duration(millis: u128) -> String {
    const HOUR: u128 = 3_600_000;
    const DAY: u128 = 24 * HOUR;
    if millis.is_multiple_of(DAY) {
        let days = millis / DAY;
        format!(
            "{days} day{} ({} hours)",
            if days == 1 { "" } else { "s" },
            days * 24
        )
    } else if millis.is_multiple_of(HOUR) {
        format!("{} hours", millis / HOUR)
    } else {
        format!("{}.{:02} hours", millis / HOUR, millis % HOUR * 100 / HOUR)
    }
}
