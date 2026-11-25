use rustc_parse::lexer::StripTokens;
use rustc_session::parse::ParseSess;
use rustc_span::{FileName, create_session_globals_then, edition::Edition};

use crate::{LintError, SourceInput};

pub(crate) fn parse<R>(input: &SourceInput, analyze: impl FnOnce() -> R) -> Result<R, LintError> {
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
                match parser.parse_crate_mod() {
                    Ok(_) => (),
                    Err(error) => {
                        error.cancel();
                        return Err(LintError::Parse {
                            name: input.name.to_string(),
                        });
                    }
                };
                Ok(analyze())
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
