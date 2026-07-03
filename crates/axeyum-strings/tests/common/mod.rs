//! Shared helpers for the `axeyum-strings` T-B.1 tests.
//!
//! Included via `mod common;` in each integration-test binary; not every binary
//! uses every helper, so unused-in-one-binary items are expected.
#![allow(dead_code)]

use axeyum_ir::{ArraySortKey, Assignment, Op, Sort, TermArena, TermId, TermNode, eval};

/// The element key used throughout the tests: 8-bit "characters".
pub const ELEM: ArraySortKey = ArraySortKey::BitVec(8);

/// The sequence sort over [`ELEM`].
#[must_use]
pub fn seq_sort() -> Sort {
    Sort::Seq(ELEM)
}

/// Declares a fresh `Seq(BitVec 8)` variable term.
#[must_use]
pub fn seq_var(arena: &mut TermArena, name: &str) -> TermId {
    let s = arena.declare(name, seq_sort()).expect("declare seq var");
    arena.var(s)
}

/// Declares a fresh `BitVec 8` (scalar element) variable term.
#[must_use]
pub fn bv_var(arena: &mut TermArena, name: &str) -> TermId {
    arena.bv_var(name, 8).expect("declare bv var")
}

/// An 8-bit character constant.
#[must_use]
pub fn ch(arena: &mut TermArena, value: u128) -> TermId {
    arena.bv_const(8, value).expect("bv const")
}

/// `seq.unit` of a term (panics on a sort error — tests only pass scalars).
#[must_use]
pub fn unit(arena: &mut TermArena, e: TermId) -> TermId {
    arena.seq_unit(e).expect("seq.unit")
}

/// `str.++` of two sequences (panics on a sort error — tests only pass matching
/// sequences).
#[must_use]
pub fn cat(arena: &mut TermArena, a: TermId, b: TermId) -> TermId {
    arena.seq_concat(a, b).expect("str.++")
}

/// The empty sequence over [`ELEM`].
#[must_use]
pub fn empty(arena: &mut TermArena) -> TermId {
    arena.seq_empty(ELEM)
}

/// Whether `term` evaluates closed under the ground evaluator (the test-side
/// mirror of the crate's private `is_constant`).
#[must_use]
pub fn is_const(arena: &TermArena, term: TermId) -> bool {
    eval(arena, term, &Assignment::new()).is_ok()
}

/// Every term reachable from `root` (including `root`), each once.
#[must_use]
pub fn all_subterms(arena: &TermArena, root: TermId) -> Vec<TermId> {
    let mut seen = std::collections::HashSet::new();
    let mut order = Vec::new();
    let mut stack = vec![root];
    while let Some(t) = stack.pop() {
        if !seen.insert(t) {
            continue;
        }
        order.push(t);
        if let TermNode::App { args, .. } = arena.node(t) {
            for &a in args {
                stack.push(a);
            }
        }
    }
    order
}

/// Whether `t` is a `str.++` node.
#[must_use]
pub fn is_concat(arena: &TermArena, t: TermId) -> bool {
    matches!(
        arena.node(t),
        TermNode::App {
            op: Op::SeqConcat,
            ..
        }
    )
}

/// Whether `t` is a `seq.empty` node.
#[must_use]
pub fn is_empty_seq(arena: &TermArena, t: TermId) -> bool {
    matches!(
        arena.node(t),
        TermNode::App {
            op: Op::SeqEmpty(_),
            ..
        }
    )
}

/// Asserts the full structural normal-form invariant on `n` (assumed to be the
/// output of `normalize`):
///
/// * **drop-ε**: no `str.++` has a `seq.empty` child;
/// * **flatten / right-association**: no `str.++` has a *non-constant* `str.++`
///   as its **left** child (constant blocks are single components and may sit on
///   the left);
/// * **fuse**: no two adjacent components of the flat view are both constant.
pub fn assert_normal_form(arena: &TermArena, n: TermId) {
    for t in all_subterms(arena, n) {
        if let TermNode::App {
            op: Op::SeqConcat,
            args,
        } = arena.node(t)
        {
            let (l, r) = (args[0], args[1]);
            assert!(!is_empty_seq(arena, l), "ε left child survived in {t:?}");
            assert!(!is_empty_seq(arena, r), "ε right child survived in {t:?}");
            assert!(
                !is_concat(arena, l) || is_const(arena, l),
                "non-constant ++ on the left child (not right-associated) in {t:?}"
            );
        }
    }

    let comps = axeyum_strings::concat_components(arena, n);
    for w in comps.windows(2) {
        assert!(
            !(is_const(arena, w[0]) && is_const(arena, w[1])),
            "two adjacent constant components survived fusion"
        );
    }
    for &c in &comps {
        assert!(!is_empty_seq(arena, c), "ε survived as a component");
        assert!(
            !is_concat(arena, c) || is_const(arena, c),
            "a component is a non-constant ++ (flatten incomplete)"
        );
    }
}
