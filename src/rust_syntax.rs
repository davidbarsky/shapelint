use rustc_ast::{Crate, ast};
use rustc_parse::lexer::StripTokens;
use rustc_session::parse::ParseSess;
use rustc_span::{
    FileName, Span, create_session_globals_then, edition::Edition, source_map::SourceMap,
};

use crate::{LintError, SourceInput};

pub(crate) struct RustFile<'a> {
    pub krate: &'a Crate,
    pub source_map: &'a SourceMap,
    pub text: &'a str,
}

impl RustFile<'_> {
    pub fn named_item(&self, item: &ast::Item) -> Option<(crate::Span, String)> {
        let name = match &item.kind {
            ast::ItemKind::Struct(name, _, _) => format!("struct {name}"),
            ast::ItemKind::Enum(name, _, _) => format!("enum {name}"),
            ast::ItemKind::Static(value) => format!("static {}", value.ident),
            ast::ItemKind::TyAlias(value) => format!("type {}", value.ident),
            ast::ItemKind::Trait(value) => format!("trait {}", value.ident),
            _ => return None,
        };
        Some((self.item_span(item.span, &item.attrs), name))
    }

    pub fn item_span(&self, span: Span, attrs: &[rustc_ast::Attribute]) -> crate::Span {
        let start = attrs
            .iter()
            .filter(|attr| attr.style == rustc_ast::AttrStyle::Outer)
            .map(|attr| attr.span.lo())
            .min();
        self.span(match start {
            Some(start) => span.with_lo(start.min(span.lo())),
            None => span,
        })
    }

    pub fn span(&self, span: Span) -> crate::Span {
        let source = self.source_map.lookup_source_file(span.lo());
        crate::Span {
            start: source.original_relative_byte_pos(span.lo()).0,
            end: source.original_relative_byte_pos(span.hi()).0,
        }
    }

    pub fn text(&self, span: Span) -> &str {
        let span = self.span(span);
        &self.text[std::ops::Range::from(span)]
    }
}

pub(crate) fn parse<R>(
    input: &SourceInput,
    analyze: impl FnOnce(&RustFile<'_>) -> R,
) -> Result<R, LintError> {
    let result = rustc_driver::catch_fatal_errors(|| {
        create_session_globals_then(Edition::Edition2024, &[], None, || {
            let session = ParseSess::new();
            session.dcx().make_silent();
            let result = (|| {
                let mut parser = match rustc_parse::new_parser_from_source_str(
                    &session,
                    FileName::Custom(input.name.to_string()),
                    input.as_ref().to_owned(),
                    StripTokens::Shebang,
                ) {
                    Ok(parser) => parser,
                    Err(errors) => {
                        for error in errors {
                            error.cancel();
                        }
                        return Err(LintError::Parse {
                            name: input.name.to_string(),
                        });
                    }
                };
                let krate = match parser.parse_crate_mod() {
                    Ok(krate) => krate,
                    Err(error) => {
                        error.cancel();
                        return Err(LintError::Parse {
                            name: input.name.to_string(),
                        });
                    }
                };
                let file = RustFile {
                    krate: &krate,
                    source_map: session.source_map(),
                    text: input.as_ref(),
                };
                Ok(analyze(&file))
            })();
            session.dcx().reset_err_count();
            result
        })
    });
    match result {
        Ok(result) => result,
        Err(_) => Err(LintError::Parse {
            name: input.name.to_string(),
        }),
    }
}

pub(crate) fn is_test_path(path: &str) -> Option<()> {
    let p = path.replace('\\', "/");
    [
        p.contains("/tests/"),
        p.starts_with("tests/"),
        p.ends_with("/tests.rs"),
        p == "tests.rs",
        p.ends_with("_test.rs"),
        p.ends_with("/test.rs"),
    ]
    .into_iter()
    .find(|matched| *matched)
    .map(|_| ())
}

pub(crate) fn test_attributes(attrs: &[ast::Attribute]) -> Option<()> {
    for attr in attrs {
        let Some(meta) = attr.meta() else { continue };
        if let Some(last) = meta.path.segments.last()
            && last.ident.name.as_str() == "test"
        {
            return Some(());
        }
        if let Some(last) = meta.path.segments.last()
            && last.ident.name.as_str() == "cfg"
            && let ast::MetaItemKind::List(items) = meta.kind
            && let [ast::MetaItemInner::MetaItem(item)] = items.as_slice()
            && let CfgTruth::Disabled = cfg_without_test(item)
        {
            return Some(());
        }
    }
    None
}
#[derive(Clone, Copy)]
enum CfgTruth {
    Enabled,
    Disabled,
    Unknown,
}
fn cfg_without_test(meta: &ast::MetaItem) -> CfgTruth {
    let Some(last) = meta.path.segments.last() else {
        return CfgTruth::Unknown;
    };
    let name = last.ident.name.as_str();
    match &meta.kind {
        ast::MetaItemKind::Word => match name {
            "test" | "false" => CfgTruth::Disabled,
            "true" => CfgTruth::Enabled,
            _ => CfgTruth::Unknown,
        },
        ast::MetaItemKind::NameValue(_) => CfgTruth::Unknown,
        ast::MetaItemKind::List(items) => {
            if name == "not" {
                return match items.as_slice() {
                    [ast::MetaItemInner::MetaItem(item)] => match cfg_without_test(item) {
                        CfgTruth::Enabled => CfgTruth::Disabled,
                        CfgTruth::Disabled => CfgTruth::Enabled,
                        CfgTruth::Unknown => CfgTruth::Unknown,
                    },
                    _ => CfgTruth::Unknown,
                };
            }
            let mut result = match name {
                "all" => CfgTruth::Enabled,
                "any" => CfgTruth::Disabled,
                _ => return CfgTruth::Unknown,
            };
            for item in items {
                let value = match item {
                    ast::MetaItemInner::MetaItem(item) => cfg_without_test(item),
                    ast::MetaItemInner::Lit(_) => CfgTruth::Unknown,
                };
                result = match (name, result, value) {
                    ("all", CfgTruth::Disabled, _) | ("all", _, CfgTruth::Disabled) => {
                        CfgTruth::Disabled
                    }
                    ("any", CfgTruth::Enabled, _) | ("any", _, CfgTruth::Enabled) => {
                        CfgTruth::Enabled
                    }
                    (_, CfgTruth::Unknown, _) | (_, _, CfgTruth::Unknown) => CfgTruth::Unknown,
                    ("all", CfgTruth::Enabled, CfgTruth::Enabled) => CfgTruth::Enabled,
                    ("any", CfgTruth::Disabled, CfgTruth::Disabled) => CfgTruth::Disabled,
                    _ => unreachable!("only all and any reach the fold"),
                };
            }
            result
        }
    }
}
