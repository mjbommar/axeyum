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

/// Flattens a right- or left-nested binary spine ITERATIVELY, leaves left to
/// right, given a predicate that recognises a spine node and yields its two
/// operands.
///
/// The family this generalises is large — `and`/`or` conjunct and disjunct
/// collectors appear across `array_axiom`, `abv`, `quant_residue_cert` and
/// `quant_bv_model_sat_cert`, each independently written as native recursion
/// over the spine's depth. That depth is attacker- and generator-controlled: an
/// SMT-LIB front end reproduces `(and (and (and …) p) q)` verbatim, so a 50k
/// conjunct source is 50k frames. Eleven such sites were found aborting the
/// process on real benchmarks; converting them one at a time invites the next
/// one to be written recursively again, so new spine walkers should call this.
///
/// Order is preserved exactly: the right operand is pushed first so operands
/// pop left to right, matching what the recursive form produced. Callers index
/// into `out`, so this is a correctness property, not a cosmetic one.
pub(crate) fn flatten_binary_spine<F>(
    arena: &TermArena,
    term: TermId,
    out: &mut Vec<TermId>,
    spine_operands: F,
) where
    F: Fn(&TermArena, TermId) -> Option<(TermId, TermId)>,
{
    let mut stack = vec![term];
    while let Some(current) = stack.pop() {
        match spine_operands(arena, current) {
            Some((left, right)) => {
                stack.push(right);
                stack.push(left);
            }
            None => out.push(current),
        }
    }
}

/// The operands of a binary `op` application, if `term` is one.
///
/// The common predicate for [`flatten_binary_spine`]; a caller needing extra
/// conditions (a sort check, a polarity check) writes its own closure.
pub(crate) fn binary_op_operands(
    arena: &TermArena,
    term: TermId,
    op: Op,
) -> Option<(TermId, TermId)> {
    match arena.node(term) {
        TermNode::App { op: found, args } if *found == op && args.len() == 2 => {
            Some((args[0], args[1]))
        }
        _ => None,
    }
}

/// Flattens an N-ARY `op` spine iteratively, leaves left to right.
///
/// The sibling of [`flatten_binary_spine`] for the plain case: no extra
/// condition, any arity. `BoolAnd`/`BoolOr` are variadic in this IR, so a
/// collector written for arity 2 silently treats a 3-argument `or` as a leaf —
/// which is a correctness bug on top of the stack-depth one, and why these are
/// two functions rather than one with an arity assumption baked in.
///
/// Operands are pushed in reverse so they pop left to right, matching the
/// recursive form callers replaced.
pub(crate) fn flatten_op_spine(arena: &TermArena, term: TermId, out: &mut Vec<TermId>, op: Op) {
    let mut stack = vec![term];
    while let Some(current) = stack.pop() {
        match arena.node(current) {
            TermNode::App { op: found, args } if *found == op => {
                for &arg in args.iter().rev() {
                    stack.push(arg);
                }
            }
            _ => out.push(current),
        }
    }
}
