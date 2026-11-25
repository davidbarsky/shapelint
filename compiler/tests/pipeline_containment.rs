#![feature(rustc_private)]

extern crate rustc_hir;
extern crate rustc_span;

use rustc_hir::def_id::{DefIndex, LocalDefId};
use rustc_span::{BytePos, Span};
use shapelint_driver::pipeline::CoveredIndex;

fn span(start: u8, end: u8) -> Span {
    Span::with_root_ctxt(
        BytePos(u32::from(start.min(end))),
        BytePos(u32::from(start.max(end))),
    )
}

#[test]
fn a_gap_between_originals_is_uncovered() {
    let owner = LocalDefId {
        local_def_index: DefIndex::from_usize(0),
    };
    let mut index = CoveredIndex::default();
    index.insert(owner, span(100, 200), span(10, 15));
    index.insert(owner, span(110, 190), span(30, 40));
    assert_eq!(index.covering_end(owner, span(20, 25)), None);
}

#[hegel::test]
fn original_span_coverage_matches_a_linear_scan(tc: hegel::TestCase) {
    let (intervals, (lo, hi)) = tc.draw(hegel::generators::default::<(Vec<(u8, u8)>, (u8, u8))>());
    let owner = LocalDefId {
        local_def_index: DefIndex::from_usize(0),
    };
    let mut index = CoveredIndex::default();
    let mut originals = Vec::new();
    for (start, end) in intervals {
        let original = span(start, end);
        index.insert(owner, span(0, u8::MAX), original);
        originals.push(original);
    }
    let query = span(lo, hi);
    let expected = originals
        .iter()
        .filter(|candidate| candidate.contains(query))
        .map(|candidate| candidate.hi())
        .max();
    assert_eq!(index.covering_end(owner, query), expected);
}

// shapelint: allow(arbitrary-bound) This threshold is the explicit logarithmic work gate.
#[test]
fn nested_nonduplicate_regions_use_logarithmic_containment_queries() {
    let owner = LocalDefId {
        local_def_index: DefIndex::from_usize(0),
    };
    let count = 1_024u32;
    let mut index = CoveredIndex::default();
    for offset in 0..count {
        let outer = Span::with_root_ctxt(BytePos(offset), BytePos(count * 2 - offset));
        let original =
            Span::with_root_ctxt(BytePos(10_000 + offset * 2), BytePos(10_001 + offset * 2));
        assert_eq!(outer.lo(), BytePos(offset));
        assert_eq!(outer.hi(), BytePos(count * 2 - offset));
        index.advance(outer);
        assert_eq!(index.covering_end(owner, original), None);
        index.insert(owner, outer, original);
    }
    let comparisons = index.comparisons(owner);
    assert!(
        comparisons < usize::try_from(count).unwrap() * 64,
        "indexed containment work must not follow the active ancestor count: {comparisons}"
    );
}

#[test]
fn nested_original_spans_still_suppress_evidence() {
    let owner = LocalDefId {
        local_def_index: DefIndex::from_usize(0),
    };
    let mut index = CoveredIndex::default();
    let outer = Span::with_root_ctxt(BytePos(0), BytePos(100));
    let original_outer = Span::with_root_ctxt(BytePos(200), BytePos(300));
    index.insert(owner, outer, original_outer);
    let original_inner = Span::with_root_ctxt(BytePos(220), BytePos(280));
    assert_eq!(
        index.covering_end(owner, original_inner),
        Some(BytePos(300))
    );
    index.advance(Span::with_root_ctxt(BytePos(101), BytePos(102)));
    assert_eq!(index.covering_end(owner, original_inner), None);
}
