#![feature(rustc_private)]

extern crate rustc_data_structures;
extern crate rustc_driver;
extern crate rustc_span;

use rustc_data_structures::sync::FreezeLock;
use rustc_span::{
    BytePos, ExternalSource, ExternalSourceKind, FileName, SourceFile, SourceFileHashAlgorithm,
};
use shapelint::LintError;
use shapelint_driver::diagnostics::Sources;
use std::sync::Arc;

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum Encoding {
    Lf,
    CrLf,
    BomLf,
    BomCrLf,
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum Part {
    Ascii,
    Unicode,
    Newline,
}

#[derive(Debug, hegel::DefaultGenerator)]
struct Document {
    encoding: Encoding,
    parts: Vec<Part>,
}

impl std::fmt::Display for Document {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.encoding {
            Encoding::BomLf | Encoding::BomCrLf => f.write_str("\u{feff}")?,
            Encoding::Lf | Encoding::CrLf => {}
        }
        for part in &self.parts {
            f.write_str(match part {
                Part::Ascii => "source",
                Part::Unicode => "λ🦀",
                Part::Newline => match self.encoding {
                    Encoding::Lf | Encoding::BomLf => "\n",
                    Encoding::CrLf | Encoding::BomCrLf => "\r\n",
                },
            })?;
        }
        f.write_str("marker")
    }
}

#[hegel::test]
fn cached_sources_share_original_bytes_and_names(tc: hegel::TestCase) {
    let document = tc.draw(hegel::generators::default::<Document>());
    rustc_span::create_default_session_globals_then(|| {
        let text = document.to_string();
        let file = SourceFile::new(
            FileName::Custom("shared.rs".into()),
            text.clone(),
            SourceFileHashAlgorithm::Sha256,
            None,
        )
        .expect("source fits rustc offsets");
        let sources = Sources::default();
        let first = sources.input(&file).expect("local source");
        let second = sources.input(&file).expect("cached local source");
        assert!(std::ptr::eq(first.as_ref(), second.as_ref()));
        assert!(Arc::ptr_eq(&first.name, &second.name));
        assert_eq!(first.as_ref(), text);

        let normalized = file.src.as_ref().expect("local source");
        let start = BytePos((normalized.len() - "marker".len()) as u32);
        let end = BytePos(normalized.len() as u32);
        let start = file.original_relative_byte_pos(start).0 as usize;
        let end = file.original_relative_byte_pos(end).0 as usize;
        assert_eq!(start, text.len() - "marker".len());
        assert_eq!(&second.as_ref()[start..end], "marker");

        #[derive(serde::Serialize)]
        struct Wire<'a> {
            name: &'a str,
            text: &'a str,
        }
        let expected = Wire {
            name: first.name.as_ref(),
            text: &text,
        };
        assert_eq!(
            serde_json::to_value(&first).expect("source JSON"),
            serde_json::to_value(expected).expect("wire contract")
        );
    });
}

#[hegel::test]
fn source_identity_includes_original_contents(tc: hegel::TestCase) {
    let document = tc.draw(hegel::generators::default::<Document>());
    rustc_span::create_default_session_globals_then(|| {
        let original = document.to_string();
        let changed = format!("{original} changed");
        let first = SourceFile::new(
            FileName::Custom("same.rs".into()),
            original.clone(),
            SourceFileHashAlgorithm::Sha256,
            None,
        )
        .expect("first source");
        let second = SourceFile::new(
            FileName::Custom("same.rs".into()),
            changed.clone(),
            SourceFileHashAlgorithm::Sha256,
            None,
        )
        .expect("second source");
        assert_eq!(first.start_pos, second.start_pos);
        assert_eq!(first.stable_id, second.stable_id);
        let sources = Sources::default();
        let first = sources.input(&first).expect("first revision");
        let second = sources.input(&second).expect("second revision");
        assert_eq!(first.as_ref(), original);
        assert_eq!(second.as_ref(), changed);
        assert_ne!(first.as_ref().as_ptr(), second.as_ref().as_ptr());
    });
}

#[hegel::test]
fn an_unavailable_source_can_be_loaded_later(tc: hegel::TestCase) {
    let document = tc.draw(hegel::generators::default::<Document>());
    rustc_span::create_default_session_globals_then(|| {
        let text = document.to_string();
        let mut file = SourceFile::new(
            FileName::Custom("external.rs".into()),
            text.clone(),
            SourceFileHashAlgorithm::Sha256,
            None,
        )
        .expect("source");
        let normalized = file.src.take().expect("local normalized bytes");
        file.external_src = FreezeLock::new(ExternalSource::Foreign {
            kind: ExternalSourceKind::AbsentOk,
            metadata_index: 0,
        });
        let sources = Sources::default();
        match sources.input(&file) {
            Err(LintError::Unavailable { name }) => assert!(name.contains("external.rs")),
            result => panic!("expected unavailable source, got {result:?}"),
        }
        file.external_src = FreezeLock::new(ExternalSource::Foreign {
            kind: ExternalSourceKind::Present(normalized),
            metadata_index: 0,
        });
        let loaded = sources.input(&file).expect("loaded external source");
        assert_eq!(loaded.as_ref(), text);
        assert!(std::ptr::eq(
            loaded.as_ref(),
            sources
                .input(&file)
                .expect("cached external source")
                .as_ref()
        ));
    });
}
