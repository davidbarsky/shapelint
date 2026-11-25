#![feature(rustc_private)]

mod support;

use std::ops::Range;

use serde::Deserialize;

#[derive(Debug, Deserialize)]
struct Diagnostic {
    rule: String,
    message: String,
    primary: Label,
    labels: Vec<Label>,
}

#[derive(Debug, Deserialize)]
struct Label {
    span: Range<usize>,
}

fn field_leaks(text: &str) -> Vec<Diagnostic> {
    support::analyze(text, &[])
        .expect("analyze fixture")
        .lines()
        .map(|line| serde_json::from_str::<Diagnostic>(line).expect("diagnostic"))
        .filter(|finding| finding.rule == "field-leak")
        .collect()
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum Access {
    DirectWrite,
    Index,
    MutableBorrow,
    Method,
    QualifiedMethod,
    Getter,
    QualifiedGetter,
    ReturningLocal,
    Setter,
    Callback,
    TupleGetter,
    TupleProjection,
    UnusedTupleMember,
    MatchedTuple,
    MutableTuple,
    OverwrittenTuple,
    BorrowedLocal,
    CapturedLoan,
    SharedCallback,
    CopiedNewtype,
    CopiedTupleMember,
    DestructuredWrite,
    DestructuredCopy,
    Read,
    CopiedGetter,
    BorrowPlainData,
    Clone,
    OwnerOperation,
    Suppressed,
    Generated,
}

#[hegel::test]
fn reports_work_done_on_another_types_representation(tc: hegel::TestCase) {
    let access = tc.draw(hegel::generators::default::<Access>());
    let (body, directive, expected) = match access {
        Access::DirectWrite => ("q.head += 1;", "", Some("head")),
        Access::Index => ("let _ = q.items[0];", "", Some("items")),
        Access::MutableBorrow => ("let _ = &mut q.items;", "", Some("items")),
        Access::Method => ("q.items.push(7);", "", Some("items")),
        Access::QualifiedMethod => ("let _ = Vec::len(&q.items);", "", Some("items")),
        Access::Getter => ("q.elements().len();", "", Some("elements")),
        Access::QualifiedGetter => ("Queue::elements(q).len();", "", Some("Queue::elements")),
        Access::ReturningLocal => ("q.storage().len();", "", Some("storage")),
        Access::Setter => ("q.rewind(q.head);", "", Some("rewind")),
        Access::Callback => ("q.edit(|items| items.push(7));", "", Some("edit")),
        Access::TupleGetter => ("let (_, head) = q.parts(); *head += 1;", "", Some("parts")),
        Access::TupleProjection => ("let _ = q.parts().0.len();", "", Some("parts")),
        Access::UnusedTupleMember => (
            "let (items, _) = q.parts(); let _ = items.len();",
            "",
            Some("parts"),
        ),
        Access::MatchedTuple => (
            "let _ = match q.parts() { (items, _) => items.len() };",
            "",
            Some("parts"),
        ),
        Access::MutableTuple => (
            "let mut parts = q.parts(); if switch { parts = other.parts(); } let _ = parts.0.len();",
            "",
            Some("parts"),
        ),
        Access::OverwrittenTuple => (
            "let mut parts = q.parts(); let _ = *parts.1; parts = other.parts(); let _ = parts.0.len();",
            "",
            Some("parts"),
        ),
        Access::BorrowedLocal => (
            "let items = q.elements(); let alias = items; let _ = alias.len();",
            "",
            Some("elements"),
        ),
        Access::CapturedLoan => (
            "let items = q.elements(); let first = || items[0]; first();",
            "",
            Some("elements"),
        ),
        Access::SharedCallback => ("q.with(|items| items[0]);", "", Some("with")),
        Access::CopiedNewtype => ("let limit = *q.maximum(); let _ = limit.0;", "", None),
        Access::CopiedTupleMember => (
            "let (_, head) = q.parts(); let value = *head; let _ = value;",
            "",
            None,
        ),
        Access::DestructuredWrite => (
            "let Queue { items, .. } = q; items.push(1);",
            "",
            Some("items"),
        ),
        Access::DestructuredCopy => (
            "let Queue { head, .. } = q; let value = *head; let _ = value;",
            "",
            None,
        ),
        Access::Read => ("let _ = q.head;", "", None),
        Access::CopiedGetter => ("let _ = q.position().count_ones();", "", None),
        Access::BorrowPlainData => ("let _ = &q.items;", "", None),
        Access::Clone => ("let _ = q.items.clone();", "", None),
        Access::OwnerOperation => ("q.pop();", "", None),
        Access::Suppressed => ("q.items.push(7);", "// shapelint: allow(field-leak)", None),
        Access::Generated => (
            "macro_rules! fill { () => { q.items.push(7) } } fill!();",
            "",
            None,
        ),
    };
    let parameters = match access {
        Access::MutableTuple => "q: &mut Queue, other: &mut Queue, switch: bool",
        Access::OverwrittenTuple => "q: &mut Queue, other: &mut Queue",
        _ => "q: &mut Queue",
    };
    let source = format!(
        r#"
        #![allow(unused_must_use)]
        #[derive(Clone, Copy)]
        pub struct Limit(usize);
        pub struct Queue {{ pub items: Vec<u8>, pub head: usize, limit: Limit }}
        impl Queue {{
            pub fn full(&self) -> bool {{ self.items.len() - self.head >= self.limit.0 }}
            pub fn pop(&mut self) -> Option<u8> {{
                let item = self.items.get(self.head).copied()?;
                self.head += 1;
                Some(item)
            }}
            pub fn elements(&self) -> &Vec<u8> {{ &self.items }}
            pub fn storage(&self) -> &Vec<u8> {{ let items = &self.items; items }}
            pub fn position(&self) -> usize {{ self.head }}
            pub fn maximum(&self) -> &Limit {{ &self.limit }}
            pub fn rewind(&mut self, head: usize) {{ self.head = head; }}
            pub fn edit(&mut self, f: impl FnOnce(&mut Vec<u8>)) {{ f(&mut self.items) }}
            pub fn with<R>(&self, f: impl FnOnce(&Vec<u8>) -> R) -> R {{ f(&self.items) }}
            pub fn parts(&mut self) -> (&Vec<u8>, &mut usize) {{ (&self.items, &mut self.head) }}
        }}
        {directive}
        pub fn consumer({parameters}) {{ {body} }}
    "#
    );
    let diagnostics = field_leaks(&source);
    let labels: Vec<_> = diagnostics
        .iter()
        .map(|d| &source[d.primary.span.clone()])
        .collect();
    assert_eq!(
        labels,
        expected.into_iter().collect::<Vec<_>>(),
        "{access:?}: {diagnostics:?}"
    );
    match access {
        Access::TupleGetter => assert!(diagnostics[0].message.contains("Queue::head")),
        Access::TupleProjection | Access::UnusedTupleMember | Access::MatchedTuple => {
            assert!(diagnostics[0].message.contains("Queue::items"));
        }
        Access::MutableTuple => {
            let [other] = diagnostics[0].labels.as_slice() else {
                panic!("{diagnostics:?}")
            };
            assert_eq!(
                other.span.start,
                source
                    .find("other.parts()")
                    .expect("conditional assignment")
                    + "other.".len()
            );
            assert!(diagnostics[0].message.contains("Queue::items"));
        }
        Access::OverwrittenTuple => {
            assert!(diagnostics[0].labels.is_empty(), "{diagnostics:?}");
            assert_eq!(
                diagnostics[0].primary.span.start,
                source.find("other.parts()").expect("definite assignment") + "other.".len()
            );
            assert!(diagnostics[0].message.contains("Queue::items"));
        }
        _ => {}
    }
}

#[test]
fn labels_every_outside_operation_on_the_field_once() {
    let source = r#"
        pub struct Table { pub rows: Vec<u8>, limit: usize }
        impl Table {
            pub fn has_room(&self) -> bool { self.rows.len() < self.limit }
        }
        pub fn insert(t: &mut Table) { t.rows.push(7); }
        pub fn first(t: &Table) -> u8 { t.rows[0] }
    "#;
    let findings = field_leaks(source);
    let [leak] = findings.as_slice() else {
        panic!("{findings:?}")
    };
    assert!(leak.message.contains("Table::rows"), "{leak:?}");
    let [other] = leak.labels.as_slice() else {
        panic!("{leak:?}")
    };
    assert_eq!(
        leak.primary.span.start,
        source.find("rows.push").expect("write")
    );
    assert_eq!(other.span.start, source.find("rows[0]").expect("index"));
}

#[test]
fn distinguishes_value_views_from_operations_by_method_identity() {
    let source = r#"
        use std::cell::Cell;
        use std::sync::atomic::{AtomicUsize, Ordering};
        pub struct Gauge(u8);
        impl Gauge { pub fn get(&self) -> u8 { self.0 } }
        pub struct Meter {
            pub counter: Cell<u8>, pub updates: AtomicUsize, pub gauge: Gauge,
            pub label: String, pub detail: Option<String>, limit: u8,
            pub marker: std::marker::PhantomPinned,
        }
        impl Meter { pub fn full(&self) -> bool { self.counter.get() >= self.limit } }
        pub fn visit(m: &mut Meter) {
            let _ = m.counter.get();
            let _ = m.updates.load(Ordering::Relaxed);
            let _ = m.label.as_bytes();
            let _ = m.detail.as_ref();
            let _ = m.detail.as_deref();
            m.marker = std::marker::PhantomPinned;
            m.counter.set(7);
            let _ = m.gauge.get();
        }
    "#;
    let diagnostics = field_leaks(source);
    let labels: Vec<_> = diagnostics
        .iter()
        .map(|d| &source[d.primary.span.clone()])
        .collect();
    assert_eq!(labels, ["counter", "gauge"], "{diagnostics:?}");
    assert!(
        diagnostics.iter().all(|d| d.labels.is_empty()),
        "{diagnostics:?}"
    );
}

#[test]
fn repeated_tuple_aliases_preserve_a_single_underlying_field() {
    use std::fmt::Write;

    let mut aliases = String::from("type T0 = u8;");
    let mut bindings = String::from("let _v0 = &self.items;");
    for depth in 1..=12 {
        let previous = depth - 1;
        writeln!(
            aliases,
            "type T{depth} = (&'static T{previous}, &'static T{previous});"
        )
        .expect("type alias");
        writeln!(bindings, "let _v{depth} = (&_v{previous}, &_v{previous});")
            .expect("tuple binding");
    }
    let source = format!(
        r#"
        {aliases}
        pub struct Queue {{ pub items: Vec<u8>, pub tree: T12, limit: usize }}
        impl Queue {{
            pub fn full(&self) -> bool {{ self.items.len() >= self.limit }}
            pub fn storage(&self) -> &Vec<u8> {{ {bindings} _v0 }}
        }}
        pub fn inspect(q: &Queue) {{
            std::hint::black_box(&q.tree);
            let _ = q.storage().len();
        }}
    "#
    );
    let diagnostics = field_leaks(&source);
    let [leak] = diagnostics.as_slice() else {
        panic!("{diagnostics:?}")
    };
    assert_eq!(&source[leak.primary.span.clone()], "storage");
    assert!(
        leak.message.contains("Queue::items") && leak.labels.is_empty(),
        "{leak:?}"
    );
}

#[hegel::test]
fn allow_comments_apply_to_each_outside_operation_before_grouping(tc: hegel::TestCase) {
    #[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
    enum Allows {
        Neither,
        Insert,
        First,
        Both,
    }
    let directives = tc.draw(hegel::generators::default::<Allows>());
    let allow = "// shapelint: allow(field-leak)";
    let (insert, first, visible): (_, _, &[&str]) = match directives {
        Allows::Neither => ("", "", &["rows.push", "rows[0]"]),
        Allows::Insert => (allow, "", &["rows[0]"]),
        Allows::First => ("", allow, &["rows.push"]),
        Allows::Both => (allow, allow, &[]),
    };
    let source = format!(
        r#"
            pub struct Table {{ pub rows: Vec<u8>, limit: usize }}
            impl Table {{ pub fn full(&self) -> bool {{ self.rows.len() >= self.limit }} }}
            {insert}
            pub fn insert(t: &mut Table) {{
                let mut append = || t.rows.push(7);
                append();
            }}
            pub fn first(t: &Table) -> u8 {{
                {first}
                t.rows[0]
            }}
        "#
    );
    let findings = field_leaks(&source);
    let actual: Vec<_> = findings
        .iter()
        .flat_map(|finding| {
            std::iter::once(&finding.primary)
                .chain(&finding.labels)
                .map(|label| label.span.start)
        })
        .collect();
    let expected: Vec<_> = visible
        .iter()
        .map(|&operation| source.find(operation).unwrap())
        .collect();
    assert_eq!(actual, expected, "{findings:?}");
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum Boundary {
    PlainRecord,
    OnlyGetter,
    OnlyForwarder,
    EveryFieldUsedOutside,
    MarkerOnly,
    MovedImpl,
    SameTangle,
}

#[hegel::test]
fn requires_a_guarded_owner_and_an_outside_operation(tc: hegel::TestCase) {
    let boundary = tc.draw(hegel::generators::default::<Boundary>());
    let source = match boundary {
        Boundary::PlainRecord => {
            r#"
            pub struct Row { pub values: Vec<u8>, pub key: u8 }
            pub fn insert(r: &mut Row) { r.values.push(1); }
        "#
        }
        Boundary::OnlyGetter => {
            r#"
            pub struct Row { pub values: Vec<u8>, pub key: u8 }
            impl Row { pub fn key(&self) -> u8 { self.key } }
            pub fn insert(r: &mut Row) { r.values.push(1); }
        "#
        }
        Boundary::OnlyForwarder => {
            r#"
            pub struct Row { pub values: Vec<u8>, pub key: u8 }
            impl Row { pub fn insert(&mut self, entry: u8) { self.values.push(entry); } }
            pub fn clear(r: &mut Row) { r.values.clear(); }
        "#
        }
        Boundary::EveryFieldUsedOutside => {
            r#"
            pub struct Row { pub values: Vec<u8>, pub limit: usize }
            impl Row { pub fn has_room(&self) -> bool { self.values.len() < self.limit } }
            pub fn insert(r: &mut Row) { if r.values.len() < r.limit { r.values.push(1); } }
        "#
        }
        Boundary::MarkerOnly => {
            r#"
            pub struct Row<T> { pub values: Vec<u8>, marker: std::marker::PhantomData<T> }
            impl<T> Row<T> { pub fn first(&self) -> u8 { self.values[0] } }
            pub fn insert<T>(r: &mut Row<T>) { r.values.push(1); }
        "#
        }
        Boundary::MovedImpl => {
            r#"
            pub mod state { pub struct Row { pub values: Vec<u8>, pub limit: usize } }
            pub mod work {
                impl crate::state::Row {
                    pub fn insert(&mut self) { if self.values.len() < self.limit { self.values.push(1); } }
                }
            }
        "#
        }
        Boundary::SameTangle => {
            r#"
            pub struct Row { pub values: Vec<u8>, limit: usize }
            pub struct Clock;
            impl Row { pub fn full(&self, _: &Clock) -> bool { self.values.len() >= self.limit } }
            impl Clock { pub fn insert(&self, row: &mut Row) { row.values.push(1); } }
        "#
        }
    };
    let diagnostics = field_leaks(source);
    assert!(diagnostics.is_empty(), "{boundary:?}: {diagnostics:?}");
}
