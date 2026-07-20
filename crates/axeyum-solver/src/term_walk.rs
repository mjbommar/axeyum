use axeyum_ir::{Op, TermArena, TermId, TermNode};

/// Appends the leaves of a binary top-level Boolean conjunction left to right.
///
/// This deliberately preserves duplicates and stops at every non-`BoolAnd`
/// node. Callers with extra leaf semantics, such as asserted BV1 conjunctions,
/// must keep those semantics in their own adapter.
pub(crate) fn collect_top_binary_conjuncts(
    arena: &TermArena,
    term: TermId,
    out: &mut Vec<TermId>,
) {
    match arena.node(term) {
        TermNode::App {
            op: Op::BoolAnd,
            args,
        } if args.len() == 2 => {
            collect_top_binary_conjuncts(arena, args[0], out);
            collect_top_binary_conjuncts(arena, args[1], out);
        }
        _ => out.push(term),
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
