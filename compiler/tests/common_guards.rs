#![feature(rustc_private)]

use shapelint_driver::contracts::Order;
use shapelint_driver::contracts::graph::{ConditionNode, ExprNode, with_graph};
use shapelint_driver::sequence::Sequence;

#[derive(Debug, hegel::DefaultGenerator)]
struct Paths {
    paths: Vec<Vec<u8>>,
}

#[hegel::test(print_blob = true)]
fn common_paths_preserve_first_order_and_duplicate_occurrences(tc: hegel::TestCase) {
    let Paths { paths } = tc.draw(hegel::generators::default::<Paths>());
    let expected = match paths.split_first() {
        None => Vec::new(),
        Some((first, rest)) => first
            .iter()
            .filter(|value| rest.iter().all(|other| other.contains(value)))
            .copied()
            .collect(),
    };
    with_graph(|mut graph| {
        let zero = graph.intern_expr(ExprNode::Number(0)).unwrap();
        let paths: Vec<Sequence<_>> = paths
            .into_iter()
            .map(|path| {
                let values: Vec<_> = path
                    .into_iter()
                    .map(|value| {
                        let input = graph
                            .intern_expr(ExprNode::Argument(usize::from(value)))
                            .unwrap();
                        graph
                            .intern_condition(ConditionNode::Compare(Order::Equal, input, zero))
                            .unwrap()
                    })
                    .collect();
                graph.condition_sequences.from_iter(values).unwrap()
            })
            .collect();
        let actual = graph.common_guards(&paths).unwrap();
        let actual: Vec<_> = graph
            .condition_sequences
            .iter(actual)
            .map(|condition| match graph[*condition] {
                ConditionNode::Compare(Order::Equal, input, _) => match graph[input] {
                    ExprNode::Argument(index) => index as u8,
                    ref actual => panic!("expected argument, got {actual:?}"),
                },
                ref actual => panic!("expected equality, got {actual:?}"),
            })
            .collect();
        assert_eq!(actual, expected);
    });
}

#[test]
fn equal_growing_paths_retain_their_shared_sequence_leaves() {
    with_graph(|mut graph| {
        let zero = graph.intern_expr(ExprNode::Number(0)).unwrap();
        let mut path = Sequence::default();
        for index in 0..4096 {
            let input = graph.intern_expr(ExprNode::Argument(index)).unwrap();
            let condition = graph
                .intern_condition(ConditionNode::Compare(Order::Equal, input, zero))
                .unwrap();
            path = graph.condition_sequences.push(path, condition).unwrap();
            let result = graph.common_guards(&[path.clone(), path.clone()]).unwrap();
            assert_eq!(
                graph.condition_sequences.len(result),
                graph.condition_sequences.len(path)
            );
            let (Some(first), Some(retained_first)) = (
                graph.condition_sequences.iter(path).next(),
                graph.condition_sequences.iter(result).next(),
            ) else {
                panic!("the growing path is nonempty");
            };
            assert!(std::ptr::eq(first, retained_first));
            let (Some(last), Some(retained_last)) = (
                graph.condition_sequences.iter(path).next_back(),
                graph.condition_sequences.iter(result).next_back(),
            ) else {
                panic!("the growing path is nonempty");
            };
            assert!(std::ptr::eq(last, retained_last));
        }
    });
}
