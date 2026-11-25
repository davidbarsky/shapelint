use std::ops::Range;
use std::process::Command;
use std::str::FromStr;

use crate::{CliError, LintedSource};

struct ChangedLines(Vec<Range<u32>>);

impl FromStr for ChangedLines {
    type Err = CliError;

    fn from_str(diff: &str) -> Result<Self, Self::Err> {
        let mut ranges = Vec::new();
        for line in diff.lines() {
            if !line.starts_with("@@ ") {
                continue;
            }
            let range = line
                .split_whitespace()
                .nth(2)
                .and_then(|range| range.strip_prefix('+'))
                .ok_or_else(|| CliError::JjHunk(line.to_owned()))?;
            let (start, count) = match range.split_once(',') {
                Some(parts) => parts,
                None => (range, "1"),
            };
            let start: u32 = start
                .parse()
                .map_err(|_| CliError::JjHunk(line.to_owned()))?;
            let count: u32 = count
                .parse()
                .map_err(|_| CliError::JjHunk(line.to_owned()))?;
            let end = start
                .checked_add(count)
                .ok_or_else(|| CliError::JjHunk(line.to_owned()))?;
            if count > 0 {
                ranges.push(start..end);
            }
        }
        ranges.sort_by_key(|range| range.start);
        let mut merged: Vec<Range<u32>> = Vec::with_capacity(ranges.len());
        for range in ranges {
            match merged.last_mut() {
                Some(previous) if range.start <= previous.end => {
                    previous.end = previous.end.max(range.end);
                }
                _ => merged.push(range),
            }
        }
        Ok(Self(merged))
    }
}

pub fn retain_changed_lines(results: &mut [LintedSource]) -> Result<(), CliError> {
    for LintedSource { input, findings } in results {
        if findings.is_empty() {
            continue;
        }
        // One literal fileset per invocation avoids parsing quoted patch paths.
        let path = serde_json::to_string(&input.name)?;
        let output = Command::new("jj")
            .args([
                "diff",
                "--color=never",
                "--no-pager",
                "--ignore-working-copy",
                "--git",
                "--context=0",
                "-r",
                "@",
                "--",
            ])
            .arg(format!("file:{path}"))
            .output()
            .map_err(CliError::JjRun)?;
        if !output.status.success() {
            return Err(CliError::JjDiff(
                String::from_utf8_lossy(&output.stderr).trim().to_owned(),
            ));
        }
        let ChangedLines(ranges) = String::from_utf8_lossy(&output.stdout).parse()?;
        findings.retain(|finding| {
            let span = finding.primary.span;
            let start = span.start as usize;
            let end = (span.end as usize).saturating_sub(1).max(start);
            let last_line = finding.line
                + input.as_ref().as_bytes()[start..end]
                    .iter()
                    .filter(|&&byte| byte == b'\n')
                    .count();
            let first = ranges.partition_point(|range| range.end as usize <= finding.line);
            match ranges.get(first) {
                Some(range) => range.start as usize <= last_line,
                None => false,
            }
        });
    }
    Ok(())
}
