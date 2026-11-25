#![feature(rustc_private)]

extern crate rustc_data_structures;
extern crate rustc_driver;

use rustc_data_structures::fx::FxHashSet;
use rustc_data_structures::graph::iterate::reverse_post_order;
use rustc_data_structures::graph::vec_graph::VecGraph;
use shapelint_driver::states::schedule::Schedule;

#[derive(Debug, hegel::DefaultGenerator)]
struct Edges(Vec<(u8, u8)>);

#[hegel::test(print_blob = true)]
fn component_rounds_match_an_independent_finite_fixed_point(tc: hegel::TestCase) {
    let Edges(edges) = tc.draw(hegel::generators::default::<Edges>());
    let edges: Vec<_> = edges
        .into_iter()
        .map(|(source, target)| (usize::from(source), usize::from(target)))
        .collect();
    let count = edges
        .iter()
        .flat_map(|(source, target)| [*source, *target])
        .max()
        .map_or(1, |last| last + 1);
    let graph = VecGraph::<usize, true>::new(count, edges.clone());
    let order = reverse_post_order(&graph, 0);
    let mut schedule = Schedule::new(&graph, &order, 0);
    let mut actual = vec![FxHashSet::default(); count];
    while let Some(node) = schedule.pop() {
        let mut next = FxHashSet::from_iter([node]);
        for predecessor in graph.predecessors(node) {
            next.extend(actual[*predecessor].iter().copied());
        }
        if next != actual[node] {
            actual[node] = next;
            for &successor in graph.successors(node) {
                schedule.changed(successor);
            }
        }
    }

    let mut reachable = FxHashSet::from_iter([0]);
    let mut pending = vec![0];
    while let Some(node) = pending.pop() {
        for &(source, target) in &edges {
            if source == node && reachable.insert(target) {
                pending.push(target);
            }
        }
    }
    let mut expected = vec![FxHashSet::default(); count];
    loop {
        let previous = expected.clone();
        for &node in &reachable {
            expected[node].insert(node);
            for &(source, target) in &edges {
                if target == node {
                    expected[node].extend(previous[source].iter().copied());
                }
            }
        }
        if previous == expected {
            break;
        }
    }
    assert_eq!(actual, expected);
}

#[test]
fn nested_cycles_publish_only_stable_exits_and_ignore_unreachable_edges() {
    let graph = VecGraph::<usize, true>::new(
        8,
        vec![
            (0, 1),
            (1, 2),
            (2, 2),
            (2, 3),
            (3, 2),
            (3, 4),
            (4, 1),
            (4, 5),
            (4, 5),
            (5, 6),
            (7, 1),
        ],
    );
    let order = reverse_post_order(&graph, 0);
    let mut schedule = Schedule::new(&graph, &order, 0);
    let mut values = vec![FxHashSet::default(); 8];
    let mut visits = [0usize; 8];
    while let Some(node) = schedule.pop() {
        visits[node] += 1;
        let mut next = FxHashSet::from_iter([node]);
        for predecessor in graph.predecessors(node) {
            next.extend(values[*predecessor].iter().copied());
        }
        if values[node] != next {
            values[node] = next;
            for &target in graph.successors(node) {
                schedule.changed(target);
            }
        }
    }
    assert_eq!(values[6], FxHashSet::from_iter(0..=6));
    assert_eq!(visits[0], 1);
    assert_eq!(visits[5], 1);
    assert_eq!(visits[6], 1);
    assert_eq!(visits[7], 0);
}

#[test]
fn fanin_activation_waits_for_every_component_in_reverse_predecessor_order() {
    let graph = VecGraph::<usize, true>::new(
        6,
        vec![(0, 1), (0, 2), (0, 3), (1, 4), (2, 4), (3, 4), (4, 5)],
    );
    let order = reverse_post_order(&graph, 0);
    let mut schedule = Schedule::new(&graph, &order, 0);
    let mut visits = Vec::new();
    while let Some(node) = schedule.pop() {
        visits.push(node);
        for &target in graph.successors(node) {
            schedule.changed(target);
        }
    }
    assert_eq!(visits, [0, 3, 2, 1, 4, 5]);
}

#[test]
fn a_two_entry_irreducible_cycle_reaches_its_finite_fixed_point_before_exiting() {
    let graph = VecGraph::<usize, true>::new(
        5,
        vec![(0, 1), (0, 2), (1, 2), (2, 1), (1, 3), (2, 3), (3, 4)],
    );
    let order = reverse_post_order(&graph, 0);
    let mut schedule = Schedule::new(&graph, &order, 0);
    let mut values = vec![FxHashSet::default(); 5];
    let mut visits = [0usize; 5];
    while let Some(node) = schedule.pop() {
        visits[node] += 1;
        let mut next = FxHashSet::from_iter([node]);
        for predecessor in graph.predecessors(node) {
            next.extend(values[*predecessor].iter().copied());
        }
        if values[node] != next {
            values[node] = next;
            for &target in graph.successors(node) {
                schedule.changed(target);
            }
        }
    }
    assert_eq!(values[1], FxHashSet::from_iter([0, 1, 2]));
    assert_eq!(values[2], FxHashSet::from_iter([0, 1, 2]));
    assert_eq!(values[4], FxHashSet::from_iter(0..=4));
    assert_eq!(visits[3], 1);
    assert_eq!(visits[4], 1);
}
