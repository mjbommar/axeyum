use axeyum_ir::{Op, TermArena, TermId, TermNode};

/// Appends the leaves of a binary top-level Boolean conjunction left to right.
///
/// This deliberately preserves duplicates and stops at every non-`BoolAnd`
/// node. Callers with extra leaf semantics, such as asserted BV1 conjunctions,
/// must keep those semantics in their own adapter.
///
/// # Why this is an explicit worklist and not native recursion
///
/// The walk's depth is the *nesting depth of the conjunction spine*, which an
/// SMT-LIB front end reproduces verbatim from the source: an assertion built as
/// `(and (and (and … ) p) q)` nests once per conjunct. Native recursion
/// therefore aborted the whole process with a stack overflow on a
/// left-associated `and` chain — the same failure mode that made nine scored
/// `QF_BV/sage/app7` benchmarks die in `auto::fold_to_real_rec` before any
/// route was reached (`fcc8760d`). An abort is strictly worse than an
/// `unknown`: the solver cannot report a first-class `unknown` and a harness
/// reads the exit as a crash.
pub(crate) fn collect_top_binary_conjuncts(arena: &TermArena, term: TermId, out: &mut Vec<TermId>) {
    // `work` is a stack, so the right child is pushed first and the left child
    // pops first: the leaf order is identical to the recursive walk's.
    let mut work = vec![term];
    while let Some(t) = work.pop() {
        match arena.node(t) {
            TermNode::App {
                op: Op::BoolAnd,
                args,
            } if args.len() == 2 => {
                let (left, right) = (args[0], args[1]);
                work.push(right);
                work.push(left);
            }
            _ => out.push(t),
        }
    }
}

#[cfg(test)]
mod tests {
    use axeyum_ir::{Sort, TermArena};

    use super::collect_top_binary_conjuncts;

    #[test]
    fn flattens_nested_binary_conjunctions_left_to_right() {
        let mut arena = TermArena::new();
        let p_symbol = arena.declare("p", Sort::Bool).expect("declare p");
        let q_symbol = arena.declare("q", Sort::Bool).expect("declare q");
        let r_symbol = arena.declare("r", Sort::Bool).expect("declare r");
        let p = arena.var(p_symbol);
        let q = arena.var(q_symbol);
        let r = arena.var(r_symbol);
        let q_and_r = arena.and(q, r).expect("q and r");
        let root = arena.and(p, q_and_r).expect("p and (q and r)");

        let mut conjuncts = Vec::new();
        collect_top_binary_conjuncts(&arena, root, &mut conjuncts);

        assert_eq!(conjuncts, vec![p, q, r]);
    }

    /// A deep left-associated `and` spine must not blow the stack.
    ///
    /// The nesting depth of a conjunction is under the benchmark author's
    /// control — an SMT-LIB `(and (and (and …) p) q)` nests once per conjunct —
    /// so a natively recursive flattener aborts the process instead of letting
    /// the solver report a first-class `unknown`. The chain is far past what
    /// any recursive frame survives on the harness's thread stack, so a
    /// regression aborts the test binary rather than failing quietly.
    #[test]
    fn survives_a_deep_conjunction_spine() {
        const DEPTH: usize = 100_000;
        let mut arena = TermArena::new();
        let p_symbol = arena.declare("deep_p", Sort::Bool).expect("declare p");
        let p = arena.var(p_symbol);
        let mut acc = p;
        for _ in 0..DEPTH {
            acc = arena.and(acc, p).expect("and");
        }

        let mut conjuncts = Vec::new();
        collect_top_binary_conjuncts(&arena, acc, &mut conjuncts);

        // Every leaf is `p`, and there is one per `and` plus the innermost one.
        assert_eq!(conjuncts.len(), DEPTH + 1);
        assert!(conjuncts.iter().all(|&c| c == p));
    }

    #[test]
    fn preserves_non_conjunctions_and_duplicate_leaves() {
        let mut arena = TermArena::new();
        let p_symbol = arena.declare("p", Sort::Bool).expect("declare p");
        let p = arena.var(p_symbol);
        let not_p = arena.not(p).expect("not p");
        let repeated = arena.and(p, p).expect("p and p");

        let mut leaf = Vec::new();
        collect_top_binary_conjuncts(&arena, not_p, &mut leaf);
        assert_eq!(leaf, vec![not_p]);

        let mut duplicates = Vec::new();
        collect_top_binary_conjuncts(&arena, repeated, &mut duplicates);
        assert_eq!(duplicates, vec![p, p]);
    }
}
