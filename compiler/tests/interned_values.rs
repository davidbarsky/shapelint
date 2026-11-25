#![feature(rustc_private)]

extern crate rustc_hir;
extern crate rustc_middle;
extern crate rustc_span;

use rustc_hir::def_id::CRATE_DEF_ID;
use rustc_middle::mir::Local;
use shapelint_driver::calls::{Generic, Type};
use shapelint_driver::contracts::{Identity, Origin};
use shapelint_driver::values::{
    CallsId, FieldsId, GenericId, GenericsId, IdentityId, InstanceId, OriginId, TextId, TypeId,
    TypesId, with_values,
};

#[hegel::test(print_blob = true)]
fn canonical_values_preserve_full_origin_context(tc: hegel::TestCase) {
    let (fields, local) = tc.draw(hegel::generators::default::<(Vec<u8>, u8)>());
    let def = CRATE_DEF_ID.to_def_id();
    let origin = Origin {
        def,
        name: Some("value".into()),
        adt: Some(def),
        identity: Some(Identity {
            origin: (def, Local::from_usize(0)),
            fields: fields.into_iter().map(usize::from).collect(),
            calls: vec![(def, Local::from_usize(usize::from(local)))],
        }),
    };
    with_values(|mut values| {
        let first = values.intern_origin(&origin).unwrap();
        assert_eq!(first, values.intern_origin(&origin).unwrap());
        assert_eq!(origin, values.export_origin(first));
        let mut different = origin.clone();
        different
            .identity
            .as_mut()
            .unwrap()
            .calls
            .push((def, Local::from_usize(1)));
        assert_ne!(first, values.intern_origin(&different).unwrap());
        different = origin.clone();
        different.identity.as_mut().unwrap().fields.push(1);
        assert_ne!(first, values.intern_origin(&different).unwrap());
        different = origin.clone();
        different.name = None;
        assert_ne!(first, values.intern_origin(&different).unwrap());
        different = origin.clone();
        different.adt = None;
        assert_ne!(first, values.intern_origin(&different).unwrap());
    });
}

#[test]
fn deep_types_canonicalize_with_explicit_key_and_import_work() {
    const DEPTH: usize = 10_000;
    let mut ty = Type::Bool;
    for _ in 0..DEPTH {
        ty = Type::Array(Box::new(ty), Box::new(Generic::Parameter(3)));
    }
    let input_nodes = 2 * DEPTH + 1;
    with_values(|mut values| {
        let before_keys = values.import_key_visits();
        let before_work = values.import_visits();
        let first = values.intern_type(&ty).unwrap();
        let first_keys = values.import_key_visits() - before_keys;
        let import_visits = values.import_visits();
        assert_eq!(first_keys, input_nodes);
        assert!(import_visits - before_work >= input_nodes);
        eprintln!(
            "deep import input_nodes={input_nodes} key_visits={first_keys} import_visits={}",
            import_visits - before_work
        );
        let exported = values.export_type(first);
        let before_exported_keys = values.import_key_visits();
        assert_eq!(first, values.intern_type(&exported).unwrap());
        assert_eq!(
            values.import_key_visits() - before_exported_keys,
            input_nodes
        );
        assert_eq!(values.import_visits(), import_visits);

        let mut changed = exported.clone();
        if let Type::Array(_, length) = &mut changed {
            **length = Generic::Parameter(4);
        }
        let before_changed_keys = values.import_key_visits();
        let before_changed = values.import_visits();
        let changed_id = values.intern_type(&changed).unwrap();
        assert_ne!(changed_id, first);
        assert_eq!(
            values.import_key_visits() - before_changed_keys,
            input_nodes
        );
        assert!(values.import_visits() > before_changed);
        let before_changed_repeat_keys = values.import_key_visits();
        let after_changed = values.import_visits();
        assert_eq!(changed_id, values.intern_type(&changed).unwrap());
        assert_eq!(
            values.import_key_visits() - before_changed_repeat_keys,
            input_nodes
        );
        assert_eq!(values.import_visits(), after_changed);

        let replacement = Type::Bool;
        let before_replacement_keys = values.import_key_visits();
        let before_replacement = values.import_visits();
        let replacement_id = values.intern_type(&replacement).unwrap();
        assert_ne!(replacement_id, first);
        assert_eq!(values.import_key_visits() - before_replacement_keys, 1);
        assert!(values.import_visits() > before_replacement);
    });
}

#[test]
fn value_views_share_canonical_types_lists_and_stable_text() {
    with_values(|mut values| {
        let ty = Type::Tuple(vec![
            Type::Array(
                Box::new(Type::Parameter(0)),
                Box::new(Generic::Parameter(1)),
            ),
            Type::Ref(rustc_hir::Mutability::Not, Box::new(Type::Bool)),
        ]);
        let first = values.intern_type(&ty).unwrap();
        let text = values.intern_text("borrowed canonical text").unwrap();
        let stable = &values[text];
        let mut view = values.share();

        assert_eq!(first, view.intern_type(&ty).unwrap());
        for index in 0..1000 {
            view.intern_text(&format!("appended value {index}"))
                .unwrap();
        }
        assert_eq!(stable, "borrowed canonical text");
        assert_eq!(first, values.intern_type(&view.export_type(first)).unwrap());
    });
}

#[test]
fn handles_are_copy_and_four_bytes() {
    fn check<T: Copy>() {
        assert_eq!(std::mem::size_of::<T>(), 4);
    }
    check::<TextId<'_>>();
    check::<TypeId<'_>>();
    check::<GenericId<'_>>();
    check::<InstanceId<'_>>();
    check::<OriginId<'_>>();
    check::<IdentityId<'_>>();
    check::<TypesId<'_>>();
    check::<GenericsId<'_>>();
    check::<FieldsId<'_>>();
    check::<CallsId<'_>>();
    check::<shapelint_driver::contracts::summaries::SummaryId<'_>>();
}

#[hegel::test(print_blob = true)]
fn substitution_preserves_context_and_matches_owned_semantics(tc: hegel::TestCase) {
    let (first, second) = tc.draw(hegel::generators::default::<(u8, u8)>());
    let ty = Type::Tuple(vec![
        Type::Parameter(0),
        Type::Array(
            Box::new(Type::Parameter(1)),
            Box::new(Generic::Parameter(2)),
        ),
    ]);
    let arguments = vec![
        Generic::Type(Type::Parameter(u32::from(first))),
        Generic::Type(Type::Bool),
        Generic::Const {
            value: u128::from(second),
            ty: Type::Char,
        },
    ];
    with_values(|mut values| {
        let id = values.intern_type(&ty).unwrap();
        let args = arguments
            .iter()
            .map(|arg| values.intern_generic(arg).unwrap())
            .collect::<Vec<_>>();
        let args = values
            .intern_list::<shapelint_driver::values::GenericsId<'_>>(args)
            .unwrap();
        let result = values.substitute_type(id, args).unwrap();
        assert_eq!(
            values.export_type(result),
            Type::Tuple(vec![
                Type::Parameter(u32::from(first)),
                Type::Array(
                    Box::new(Type::Bool),
                    Box::new(Generic::Const {
                        value: u128::from(second),
                        ty: Type::Char
                    })
                )
            ])
        );
        assert_eq!(result, values.substitute_type(id, args).unwrap());
        let alternative = values
            .intern_list::<shapelint_driver::values::GenericsId<'_>>([])
            .unwrap();
        assert_eq!(values.substitute_type(id, alternative).unwrap(), id);
    });
}

#[hegel::test(print_blob = true)]
fn frozen_summaries_preserve_consumer_and_report_locations(tc: hegel::TestCase) {
    use shapelint_driver::contracts::graph::{ConditionNode, with_graph};
    use shapelint_driver::contracts::{Consumer, Operation, Requirement, Summary};
    let reason = tc.draw(hegel::generators::default::<String>());
    let def = CRATE_DEF_ID.to_def_id();
    with_graph(|mut graph| {
        let condition = graph.intern_condition(ConditionNode::Unknown).unwrap();
        let guards = shapelint_driver::sequence::Sequence::EMPTY;
        let invalidated = shapelint_driver::sequence::Sequence::EMPTY;
        let make = || Summary {
            requirements: vec![Requirement {
                invalidated,
                consumer: Consumer {
                    def,
                    span: rustc_span::DUMMY_SP,
                    operation: Operation::Unsupported(reason.clone()),
                },
                condition,
                guards,
                span: rustc_span::DUMMY_SP,
            }],
            ..Summary::default()
        };
        let first = graph
            .summaries
            .freeze(
                &mut graph.values,
                &mut graph.function_sets,
                &mut graph.input_sets,
                &mut graph.expression_sequences,
                make(),
            )
            .unwrap();
        let mut summary_view = graph.summaries.share();
        let second = summary_view
            .freeze(
                &mut graph.values,
                &mut graph.function_sets,
                &mut graph.input_sets,
                &mut graph.expression_sequences,
                make(),
            )
            .unwrap();
        assert_eq!(first, second);
        let node = graph.summaries[first];
        let requirement = graph
            .summaries
            .requirements
            .iter(node.requirements)
            .next()
            .unwrap();
        let consumer = graph
            .summaries
            .export_consumer(&graph.values, requirement.consumer);
        match consumer.operation {
            Operation::Unsupported(actual) => assert_eq!(actual, reason),
            Operation::Condition | Operation::Subtraction { .. } => {
                panic!("consumer operation changed")
            }
        }
        assert_eq!(requirement.span, rustc_span::DUMMY_SP);
    });
}
