//! Equivalence of quantified formulas up to bound-variable renaming and the
//! quantifier-negation duality.
//!
//! Two syntactic differences between formulas provably cannot change what they
//! denote, and this module decides both in one walk.
//!
//! **Bound-variable names.** The SMT-LIB front end gives *every* binder
//! occurrence a fresh arena symbol (`fresh_quantifier_symbol`), so two formulas
//! a reader would call "the same" — `(forall ((x U)) (P x))` written twice —
//! are two structurally distinct terms `forall !q.x.0. P !q.x.0` and
//! `forall !q.x.1. P !q.x.1`. Hash-consing cannot merge them: the bound symbol
//! is part of the operator.
//!
//! **Negation duality.** `not (forall x. b)` and `exists x. not b` denote the
//! same formula (`F:quantifier-negation-duality`), as do `not (exists x. b)`
//! and `forall x. not b`. The walk carries a negation *parity* — a `not` on
//! either side flips it, and at odd parity a `forall` matches an `exists` —
//! which decides the duality on the untouched terms, allocating nothing. That
//! is what lets a **checker** re-derive it independently of the canonicalizer
//! rewrite that produced the verdict.
//!
//! # Why this is the delicate half
//!
//! A wrong `true` here is a wrong-`unsat` generator: the canonicalizer folds
//! `(= p q)` to `true` on the strength of this predicate, and the
//! `bool_simplify` certificate checker accepts a refutation on it. Four failure
//! modes a naive implementation walks straight into, each covered by a negative
//! test in this module:
//!
//! * **The pointer fast path.** `left == right` is *not* sufficient once a
//!   non-identity binder correspondence is in scope. Comparing
//!   `forall x. P(x)` against `forall y. P(x)` reaches the two bodies as the
//!   *same interned term* `P(x)`, yet the formulas are inequivalent (the second
//!   leaves `x` free). The fast path is therefore taken only while the
//!   correspondence is pointwise identity, and never at odd parity.
//! * **The escaping right-hand binder.** A forward-only map accepts
//!   `forall x. P(y)` against `forall y. P(y)`: the left `y` is unmapped, the
//!   right symbol is also `y`, so "unmapped symbols must be identical" passes —
//!   but the right binds that `y` and the left does not.
//! * **One-sided shadowing.** `forall x. forall z. R(x,z)` against
//!   `forall y. forall y. R(y,y)` maps `x -> y` and `z -> y`; consulting only
//!   the left symbol finds both argument positions satisfied and wrongly
//!   accepts, though the right-hand formula is the strictly different
//!   `forall y. R(y,y)`. See [`Scope::binder_depth_right`].
//! * **Falling through at odd parity.** If the odd-parity case ever reached the
//!   ordinary structural comparison, it would accept `P(x)` against `P(x)` and
//!   thereby claim `P(x)` is its own negation. Odd parity admits exactly four
//!   shapes and declines everything else.
//!
//! The last three are all one discipline: a symbol occurrence is matched by the
//! **binder depth** that binds it on each side, never by name and never in one
//! direction only. Where the walk cannot be sure it declines (returns `false`);
//! declining can only weaken a rewrite, never unsoundly strengthen one.

use axeyum_ir::{Op, SymbolId, TermArena, TermId, TermNode};

/// The number of node comparisons [`alpha_equivalent`] performs before
/// declining.
///
/// Terms are DAGs but the comparison walk is a *tree* walk (the binder
/// correspondence in scope differs between paths, so results cannot be memoized
/// by term id alone), which is exponential in the worst case. Exhausting the
/// budget returns `false` — a decline, never an accept — so the bound trades
/// completeness for a hard time bound and can never trade away soundness.
pub const ALPHA_EQUIVALENCE_STEP_BUDGET: usize = 100_000;

/// Whether `left` and `right` denote the same term up to renaming of bound
/// variables and the quantifier-negation duality.
///
/// Returns `false` whenever the walk cannot establish equivalence, including
/// when it exhausts [`ALPHA_EQUIVALENCE_STEP_BUDGET`]. A `true` result is a
/// claim that the two terms have the same denotation under every structure and
/// every assignment to their (identical) free symbols.
///
/// ```
/// # use axeyum_ir::{Sort, TermArena};
/// # use axeyum_rewrite::alpha_equivalent;
/// let mut arena = TermArena::new();
/// let carrier = Sort::Uninterpreted(arena.declare_uninterpreted_sort("U"));
/// let p = arena.declare_fun("P", &[carrier], Sort::Bool)?;
/// let x = arena.declare("!q.x.0", carrier)?;
/// let y = arena.declare("!q.x.1", carrier)?;
///
/// // not (forall x. P x)
/// let xv = arena.var(x);
/// let px = arena.apply(p, &[xv])?;
/// let left = arena.forall(x, px)?;
/// let left = arena.not(left)?;
///
/// // exists y. not (P y)   -- a different binder, and the dual quantifier
/// let yv = arena.var(y);
/// let py = arena.apply(p, &[yv])?;
/// let not_py = arena.not(py)?;
/// let right = arena.exists(y, not_py)?;
///
/// assert_ne!(left, right);
/// assert!(alpha_equivalent(&arena, left, right));
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
#[must_use]
pub fn alpha_equivalent(arena: &TermArena, left: TermId, right: TermId) -> bool {
    let mut scope = Scope::default();
    let mut budget = ALPHA_EQUIVALENCE_STEP_BUDGET;
    alpha_eq(arena, left, right, false, &mut scope, &mut budget)
}

/// Whether `left` is equivalent to the **negation** of `right`, up to renaming
/// of bound variables and the quantifier-negation duality.
///
/// This is [`alpha_equivalent`] carrying a negation parity. It decides the
/// duality identities directly on the untouched terms — `not (forall x. P x)`
/// against `exists x. not (P x)` — without rewriting anything, which is what
/// lets a *checker* re-derive them without depending on the canonicalizer that
/// produced the verdict.
///
/// # The rule at odd parity
///
/// Writing `a ~p b` for "`a` is equivalent to `b`" at even parity and "`a` is
/// equivalent to `not b`" at odd parity, the only odd-parity steps taken are:
///
/// * peeling a `not` from either side, which flips the parity;
/// * `forall x. a ~odd exists y. b` when `a ~odd b` under `x <-> y`, because
///   `not (exists y. b)` is `forall y. not b`;
/// * `exists x. a ~odd forall y. b`, the dual;
/// * the two Boolean constants, which are each other's negation.
///
/// **Every other shape declines at odd parity.** There is deliberately no
/// fall-through to the even-parity structural comparison: that would conclude
/// `P(x) ~odd P(x)`, i.e. that `P(x)` is its own negation, which is the one
/// mistake here that manufactures wrong `unsat`s. The negative tests pin it.
#[must_use]
pub fn alpha_equivalent_to_negation(arena: &TermArena, left: TermId, right: TermId) -> bool {
    let mut scope = Scope::default();
    let mut budget = ALPHA_EQUIVALENCE_STEP_BUDGET;
    alpha_eq(arena, left, right, true, &mut scope, &mut budget)
}

/// The binder correspondence currently in scope, innermost last.
///
/// `pairs[i] = (l, r)` records that the `i`-th enclosing binder binds `l` on the
/// left and `r` on the right. Lookups scan from the end so an inner binder
/// shadows an outer one, matching the scoping the quantifier operators define.
#[derive(Default)]
struct Scope {
    pairs: Vec<(SymbolId, SymbolId)>,
    /// How many entries of `pairs` have `l != r`. While this is zero the
    /// correspondence is pointwise identity and structural equality of two
    /// terms implies alpha-equivalence, which is what licenses the pointer fast
    /// path.
    nontrivial: usize,
}

impl Scope {
    fn push(&mut self, left: SymbolId, right: SymbolId) {
        if left != right {
            self.nontrivial += 1;
        }
        self.pairs.push((left, right));
    }

    fn pop(&mut self) {
        if let Some((left, right)) = self.pairs.pop()
            && left != right
        {
            self.nontrivial -= 1;
        }
    }

    /// Which enclosing binder binds `left` on the left-hand side, innermost
    /// first, or `None` if `left` is free there.
    ///
    /// The *depth* is returned rather than the partner symbol, because matching
    /// symbols is not enough — see [`Scope::binder_depth_right`].
    fn binder_depth_left(&self, left: SymbolId) -> Option<usize> {
        self.pairs.iter().rposition(|(l, _)| *l == left)
    }

    /// Which enclosing binder binds `right` on the right-hand side.
    ///
    /// Both depths are needed, and they must be **equal**, because a one-sided
    /// lookup accepts a formula it must reject when the right-hand side shadows
    /// a binder the left-hand side does not:
    ///
    /// ```text
    /// left  = forall x. forall z. R(x, z)
    /// right = forall y. forall y. R(y, y)      -- the inner `y` shadows
    /// ```
    ///
    /// Here the correspondence is `[(x,y), (z,y)]`. Looking up only the left
    /// symbol, `x` maps to `y` and `z` maps to `y`, so both argument positions
    /// "match" and the two formulas are declared equivalent — but the right-hand
    /// one is `forall y. R(y, y)`, a strictly stronger statement. Requiring the
    /// two depths to agree rejects it: `x` is bound at depth 0 while the right's
    /// `y` resolves to depth 1.
    fn binder_depth_right(&self, right: SymbolId) -> Option<usize> {
        self.pairs.iter().rposition(|(_, r)| *r == right)
    }
}

fn alpha_eq(
    arena: &TermArena,
    left: TermId,
    right: TermId,
    negate: bool,
    scope: &mut Scope,
    budget: &mut usize,
) -> bool {
    if *budget == 0 {
        return false;
    }
    *budget -= 1;

    // Peel `not` from either side, flipping the parity. Each peel removes a node,
    // so this terminates; two `not`s (one per side) return to even parity.
    if let TermNode::App {
        op: Op::BoolNot,
        args,
    } = arena.node(left)
    {
        return alpha_eq(arena, args[0], right, !negate, scope, budget);
    }
    if let TermNode::App {
        op: Op::BoolNot,
        args,
    } = arena.node(right)
    {
        return alpha_eq(arena, left, args[0], !negate, scope, budget);
    }

    if negate {
        return alpha_eq_negated(arena, left, right, scope, budget);
    }

    // Interning makes structural equality decidable by identity, but only while
    // no binder has been renamed underneath us — see the module note on the
    // pointer fast path. (Reachable only at even parity: at odd parity two
    // identical terms are precisely *not* equivalent.)
    if scope.nontrivial == 0 && left == right {
        return true;
    }

    match (arena.node(left), arena.node(right)) {
        (TermNode::Symbol(l), TermNode::Symbol(r)) => {
            match (scope.binder_depth_left(*l), scope.binder_depth_right(*r)) {
                // Both bound: by the *same* enclosing binder, not merely by
                // binders that happen to be paired somewhere.
                (Some(left_depth), Some(right_depth)) => left_depth == right_depth,
                // Both free: the same symbol, since free symbols are shared.
                (None, None) => *l == *r,
                // One bound and one free is a mismatch however the names line
                // up — this is the case that rejects `forall x. P(y)` against
                // `forall y. P(y)`.
                _ => false,
            }
        }
        (
            TermNode::App {
                op: left_op,
                args: left_args,
            },
            TermNode::App {
                op: right_op,
                args: right_args,
            },
        ) => alpha_eq_app(
            arena,
            (*left_op, &**left_args),
            (*right_op, &**right_args),
            scope,
            budget,
        ),
        // Constants carry no symbols, so interning already decided them; any
        // other cross-variant pairing is a mismatch.
        (l, r) => l == r,
    }
}

/// The odd-parity step: is `left` equivalent to `not right`?
///
/// Called only after both sides' leading `not`s have been peeled, so neither
/// side is a `BoolNot`. The admitted shapes are exhaustive and everything else
/// declines — see the note on [`alpha_equivalent_to_negation`] for why a
/// fall-through here would be a wrong-`unsat` generator.
fn alpha_eq_negated(
    arena: &TermArena,
    left: TermId,
    right: TermId,
    scope: &mut Scope,
    budget: &mut usize,
) -> bool {
    let (left_node, right_node) = (arena.node(left), arena.node(right));

    // `true` and `false` are each other's negation.
    if let (TermNode::BoolConst(l), TermNode::BoolConst(r)) = (left_node, right_node) {
        return l != r;
    }

    // The duality itself: `not (exists y. b)` is `forall y. not b`, so
    // `forall x. a` is the negation of `exists y. b` exactly when `a` is the
    // negation of `b` under the correspondence `x <-> y`. Dually for the other
    // pairing. A `forall`/`forall` or `exists`/`exists` pairing carries no such
    // identity and is not admitted.
    let (
        TermNode::App {
            op: left_op,
            args: left_args,
        },
        TermNode::App {
            op: right_op,
            args: right_args,
        },
    ) = (left_node, right_node)
    else {
        return false;
    };
    let (l, r) = match (left_op, right_op) {
        (Op::Forall(l), Op::Exists(r)) | (Op::Exists(l), Op::Forall(r)) => (*l, *r),
        _ => return false,
    };
    if arena.symbol(l).1 != arena.symbol(r).1 {
        return false;
    }

    scope.push(l, r);
    let equivalent = alpha_eq(arena, left_args[0], right_args[0], true, scope, budget);
    scope.pop();
    equivalent
}

fn alpha_eq_app(
    arena: &TermArena,
    (left_op, left_args): (Op, &[TermId]),
    (right_op, right_args): (Op, &[TermId]),
    scope: &mut Scope,
    budget: &mut usize,
) -> bool {
    if left_args.len() != right_args.len() {
        return false;
    }

    // Quantifiers are the only operators whose payload is a *binder*: the two
    // sides may legitimately name it differently, but must agree on the
    // quantifier kind and on the bound variable's sort.
    let binders = match (left_op, right_op) {
        (Op::Forall(l), Op::Forall(r)) | (Op::Exists(l), Op::Exists(r)) => {
            if arena.symbol(l).1 != arena.symbol(r).1 {
                return false;
            }
            Some((l, r))
        }
        // A `forall` is never alpha-equivalent to an `exists`, and every
        // non-quantifier operator must match exactly (function symbols in
        // `Op::Apply`, widths, sorts, and indices included).
        _ => {
            if left_op != right_op {
                return false;
            }
            None
        }
    };

    if let Some((l, r)) = binders {
        scope.push(l, r);
    }
    let equal = left_args
        .iter()
        .zip(right_args)
        .all(|(&l, &r)| alpha_eq(arena, l, r, false, scope, budget));
    if binders.is_some() {
        scope.pop();
    }
    equal
}

#[cfg(test)]
mod tests {
    use super::{alpha_equivalent, alpha_equivalent_to_negation};
    use axeyum_ir::{FuncId, Sort, SymbolId, TermArena, TermId};

    /// A predicate `P : U -> Bool` over an uninterpreted carrier, and a fresh
    /// binder factory, mirroring what the SMT-LIB parser produces.
    struct Fixture {
        arena: TermArena,
        carrier: Sort,
        p: FuncId,
        counter: u32,
    }

    impl Fixture {
        fn new() -> Self {
            let mut arena = TermArena::new();
            let carrier = Sort::Uninterpreted(arena.declare_uninterpreted_sort("U"));
            let p = arena.declare_fun("P", &[carrier], Sort::Bool).unwrap();
            Self {
                arena,
                carrier,
                p,
                counter: 0,
            }
        }

        fn binder(&mut self) -> SymbolId {
            self.counter += 1;
            let name = format!("!q.x.{}", self.counter);
            self.arena.declare(&name, self.carrier).unwrap()
        }

        fn free(&mut self, name: &str) -> SymbolId {
            self.arena.declare(name, self.carrier).unwrap()
        }

        fn p_of(&mut self, symbol: SymbolId) -> TermId {
            let arg = self.arena.var(symbol);
            self.arena.apply(self.p, &[arg]).unwrap()
        }
    }

    #[test]
    fn renamed_binder_is_alpha_equivalent() {
        let mut f = Fixture::new();
        let (x, y) = (f.binder(), f.binder());
        let px = f.p_of(x);
        let py = f.p_of(y);
        let left = f.arena.forall(x, px).unwrap();
        let right = f.arena.forall(y, py).unwrap();
        assert_ne!(left, right, "distinct binders must not intern together");
        assert!(alpha_equivalent(&f.arena, left, right));
    }

    #[test]
    fn identical_terms_are_alpha_equivalent() {
        let mut f = Fixture::new();
        let x = f.binder();
        let px = f.p_of(x);
        let term = f.arena.forall(x, px).unwrap();
        assert!(alpha_equivalent(&f.arena, term, term));
    }

    /// NEGATIVE. The pointer fast path: both bodies are the *same interned
    /// term* `P(x)`, but only the left binds `x`. `forall x. P(x)` is a closed
    /// formula; `forall y. P(x)` is `P(x)` with `x` free. Accepting this would
    /// let the canonicalizer fold an equality between them to `true`.
    #[test]
    fn shared_body_under_renamed_binder_is_not_alpha_equivalent() {
        let mut f = Fixture::new();
        let (x, y) = (f.binder(), f.binder());
        let px = f.p_of(x);
        let left = f.arena.forall(x, px).unwrap();
        let right = f.arena.forall(y, px).unwrap();
        assert!(!alpha_equivalent(&f.arena, left, right));
        assert!(!alpha_equivalent(&f.arena, right, left));
    }

    /// NEGATIVE. The escaping right-hand binder: a forward-only correspondence
    /// accepts this, because the left `y` is unmapped and the right symbol is
    /// also `y`. But the right *binds* that `y` and the left does not.
    #[test]
    fn free_symbol_captured_on_the_right_is_not_alpha_equivalent() {
        let mut f = Fixture::new();
        let x = f.binder();
        let y = f.binder();
        let py = f.p_of(y);
        // `forall x. P(y)` — `y` free, `x` vacuous.
        let left = f.arena.forall(x, py).unwrap();
        // `forall y. P(y)` — `y` bound.
        let right = f.arena.forall(y, py).unwrap();
        assert!(!alpha_equivalent(&f.arena, left, right));
        assert!(!alpha_equivalent(&f.arena, right, left));
    }

    /// NEGATIVE. Renaming may not change the quantifier.
    #[test]
    fn forall_is_not_alpha_equivalent_to_exists() {
        let mut f = Fixture::new();
        let (x, y) = (f.binder(), f.binder());
        let px = f.p_of(x);
        let py = f.p_of(y);
        let left = f.arena.forall(x, px).unwrap();
        let right = f.arena.exists(y, py).unwrap();
        assert!(!alpha_equivalent(&f.arena, left, right));
    }

    /// NEGATIVE. Binder sorts are part of the term's meaning.
    #[test]
    fn differing_binder_sorts_are_not_alpha_equivalent() {
        let mut arena = TermArena::new();
        let q = arena.declare_fun("Q", &[Sort::Bool], Sort::Bool).unwrap();
        let narrow = arena.declare("n", Sort::BitVec(4)).unwrap();
        let wide = arena.declare("w", Sort::BitVec(8)).unwrap();
        let narrow_var = arena.var(narrow);
        let wide_var = arena.var(wide);
        let narrow_body = arena.eq(narrow_var, narrow_var).unwrap();
        let wide_body = arena.eq(wide_var, wide_var).unwrap();
        let narrow_body = arena.apply(q, &[narrow_body]).unwrap();
        let wide_body = arena.apply(q, &[wide_body]).unwrap();
        let left = arena.forall(narrow, narrow_body).unwrap();
        let right = arena.forall(wide, wide_body).unwrap();
        assert!(!alpha_equivalent(&arena, left, right));
    }

    /// NEGATIVE. Argument *order* under a renamed binder: `forall x,y. R(x,y)`
    /// against `forall a,b. R(b,a)`. The correspondence maps x->a and y->b, so
    /// the swapped occurrences must be rejected.
    #[test]
    fn swapped_bound_arguments_are_not_alpha_equivalent() {
        let mut arena = TermArena::new();
        let carrier = Sort::Uninterpreted(arena.declare_uninterpreted_sort("U"));
        let relation = arena
            .declare_fun("R", &[carrier, carrier], Sort::Bool)
            .unwrap();
        let fresh = |arena: &mut TermArena, n: &str| arena.declare(n, carrier).unwrap();
        let outer = fresh(&mut arena, "x");
        let inner = fresh(&mut arena, "y");
        let outer_renamed = fresh(&mut arena, "a");
        let inner_renamed = fresh(&mut arena, "b");

        let (xv, yv) = (arena.var(outer), arena.var(inner));
        let straight = arena.apply(relation, &[xv, yv]).unwrap();
        let left = arena.forall(inner, straight).unwrap();
        let left = arena.forall(outer, left).unwrap();

        let (av, bv) = (arena.var(outer_renamed), arena.var(inner_renamed));
        let swapped = arena.apply(relation, &[bv, av]).unwrap();
        let right = arena.forall(inner_renamed, swapped).unwrap();
        let right = arena.forall(outer_renamed, right).unwrap();

        assert!(!alpha_equivalent(&arena, left, right));

        // ...while the un-swapped renaming of the same shape *is* accepted.
        let straight_ab = arena.apply(relation, &[av, bv]).unwrap();
        let honest = arena.forall(inner_renamed, straight_ab).unwrap();
        let honest = arena.forall(outer_renamed, honest).unwrap();
        assert!(alpha_equivalent(&arena, left, honest));
    }

    /// NEGATIVE. Distinct *free* symbols are never interchangeable, even in
    /// otherwise identical quantified shells.
    #[test]
    fn distinct_free_symbols_are_not_alpha_equivalent() {
        let mut f = Fixture::new();
        let x = f.binder();
        let y = f.binder();
        let first = f.free("c");
        let second = f.free("d");
        let xv = f.arena.var(x);
        let yv = f.arena.var(y);
        let cv = f.arena.var(first);
        let dv = f.arena.var(second);
        let left_body = f.arena.eq(xv, cv).unwrap();
        let right_body = f.arena.eq(yv, dv).unwrap();
        let left = f.arena.forall(x, left_body).unwrap();
        let right = f.arena.forall(y, right_body).unwrap();
        assert!(!alpha_equivalent(&f.arena, left, right));
    }

    /// Shadowing: an inner binder that reuses the outer correspondence's
    /// *right-hand* name must resolve to the inner pairing, not the outer one.
    #[test]
    fn inner_binder_shadows_the_outer_correspondence() {
        let mut f = Fixture::new();
        let x = f.binder();
        let y = f.binder();
        let z = f.binder();
        // left: forall x. forall y. P(y)   right: forall y. forall z. P(z)
        let py = f.p_of(y);
        let left_inner = f.arena.forall(y, py).unwrap();
        let left = f.arena.forall(x, left_inner).unwrap();
        let pz = f.p_of(z);
        let right_inner = f.arena.forall(z, pz).unwrap();
        let right = f.arena.forall(y, right_inner).unwrap();
        assert!(alpha_equivalent(&f.arena, left, right));

        // ...but the outer variable is not interchangeable with the inner one:
        // left: forall x. forall y. P(x)   right: forall y. forall z. P(z)
        let px = f.p_of(x);
        let left_inner = f.arena.forall(y, px).unwrap();
        let left_outer_use = f.arena.forall(x, left_inner).unwrap();
        assert!(!alpha_equivalent(&f.arena, left_outer_use, right));
    }

    // ---------------------------------------------------------------------
    // `alpha_equivalent_to_negation` — the quantifier-duality identities.
    // ---------------------------------------------------------------------

    /// `not (forall x. P x)` **is** `exists x. not (P x)` — an equivalence, with
    /// independently fresh binders on the two sides, exactly as the SMT-LIB
    /// front end produces them. This is `F:quantifier-negation-duality`, first
    /// half.
    #[test]
    fn negated_universal_is_the_dual_existential() {
        let mut f = Fixture::new();
        let (x, y) = (f.binder(), f.binder());
        let px = f.p_of(x);
        let py = f.p_of(y);
        let universal = f.arena.forall(x, px).unwrap();
        let negated_universal = f.arena.not(universal).unwrap();
        let not_py = f.arena.not(py).unwrap();
        let dual = f.arena.exists(y, not_py).unwrap();
        assert!(alpha_equivalent(&f.arena, negated_universal, dual));
        assert!(alpha_equivalent(&f.arena, dual, negated_universal));
        // ...and they are emphatically not each other's negation.
        assert!(!alpha_equivalent_to_negation(
            &f.arena,
            negated_universal,
            dual
        ));
        // The un-negated universal *is* the negation of the dual existential.
        assert!(alpha_equivalent_to_negation(&f.arena, universal, dual));
    }

    /// `not (exists x. P x)` is `forall x. not (P x)` — second half of the fact.
    #[test]
    fn negated_existential_is_the_dual_universal() {
        let mut f = Fixture::new();
        let (x, y) = (f.binder(), f.binder());
        let px = f.p_of(x);
        let py = f.p_of(y);
        let existential = f.arena.exists(x, px).unwrap();
        let negated_existential = f.arena.not(existential).unwrap();
        let not_py = f.arena.not(py).unwrap();
        let dual = f.arena.forall(y, not_py).unwrap();
        assert!(alpha_equivalent(&f.arena, negated_existential, dual));
        assert!(alpha_equivalent(&f.arena, dual, negated_existential));
        assert!(alpha_equivalent_to_negation(&f.arena, existential, dual));
    }

    /// NEGATIVE, and the one that matters most: at odd parity a term is never
    /// its own partner. A fall-through to the even-parity structural comparison
    /// would accept these and assert that `P(x)` is equivalent to `not P(x)`.
    #[test]
    fn a_term_is_never_the_negation_of_itself() {
        let mut f = Fixture::new();
        let x = f.binder();
        let px = f.p_of(x);
        assert!(!alpha_equivalent_to_negation(&f.arena, px, px));

        let universal = f.arena.forall(x, px).unwrap();
        assert!(!alpha_equivalent_to_negation(
            &f.arena, universal, universal
        ));

        let c = f.free("c");
        let cv = f.arena.var(c);
        let refl = f.arena.eq(cv, cv).unwrap();
        assert!(!alpha_equivalent_to_negation(&f.arena, refl, refl));
    }

    /// NEGATIVE. Negation does *not* preserve the quantifier: `not (forall x. P
    /// x)` is not `forall x. not (P x)` (the second is strictly stronger), and
    /// `not (exists x. P x)` is not `exists x. not (P x)`.
    #[test]
    fn negation_that_keeps_the_quantifier_is_rejected() {
        let mut f = Fixture::new();
        let (x, y) = (f.binder(), f.binder());
        let px = f.p_of(x);
        let py = f.p_of(y);
        let not_py = f.arena.not(py).unwrap();

        let universal = f.arena.forall(x, px).unwrap();
        let negated_universal = f.arena.not(universal).unwrap();
        let same_quantifier = f.arena.forall(y, not_py).unwrap();
        assert!(!alpha_equivalent(
            &f.arena,
            negated_universal,
            same_quantifier
        ));
        assert!(!alpha_equivalent_to_negation(
            &f.arena,
            negated_universal,
            same_quantifier
        ));

        let existential = f.arena.exists(x, px).unwrap();
        let negated_existential = f.arena.not(existential).unwrap();
        let same_quantifier = f.arena.exists(y, not_py).unwrap();
        assert!(!alpha_equivalent(
            &f.arena,
            negated_existential,
            same_quantifier
        ));
        assert!(!alpha_equivalent_to_negation(
            &f.arena,
            negated_existential,
            same_quantifier
        ));
    }

    /// NEGATIVE. Flipping the quantifier without negating the body is the most
    /// tempting near-miss: `not (forall x. P x)` is `exists x. NOT (P x)`, never
    /// `exists x. P x`.
    #[test]
    fn duality_without_negating_the_body_is_rejected() {
        let mut f = Fixture::new();
        let (x, y) = (f.binder(), f.binder());
        let px = f.p_of(x);
        let py = f.p_of(y);
        let universal = f.arena.forall(x, px).unwrap();
        let negated_universal = f.arena.not(universal).unwrap();
        let bare_existential = f.arena.exists(y, py).unwrap();
        assert!(!alpha_equivalent(
            &f.arena,
            negated_universal,
            bare_existential
        ));
    }

    /// Alternating prefixes: `not (forall x. exists y. R(x,y))` is
    /// `exists x. forall y. not R(x,y)`. Both binders are renamed and both
    /// quantifiers flip, so this exercises the parity across nesting.
    #[test]
    fn duality_flips_an_alternating_prefix() {
        let mut arena = TermArena::new();
        let carrier = Sort::Uninterpreted(arena.declare_uninterpreted_sort("U"));
        let relation = arena
            .declare_fun("R", &[carrier, carrier], Sort::Bool)
            .unwrap();
        let outer = arena.declare("!q.x.0", carrier).unwrap();
        let inner_var = arena.declare("!q.y.0", carrier).unwrap();
        let outer_renamed = arena.declare("!q.x.1", carrier).unwrap();
        let inner_renamed = arena.declare("!q.y.1", carrier).unwrap();

        let (xv, yv) = (arena.var(outer), arena.var(inner_var));
        let rxy = arena.apply(relation, &[xv, yv]).unwrap();
        let inner = arena.exists(inner_var, rxy).unwrap();
        let left = arena.forall(outer, inner).unwrap();
        let left = arena.not(left).unwrap();

        let (av, bv) = (arena.var(outer_renamed), arena.var(inner_renamed));
        let rab = arena.apply(relation, &[av, bv]).unwrap();
        let not_rab = arena.not(rab).unwrap();
        let inner = arena.forall(inner_renamed, not_rab).unwrap();
        let right = arena.exists(outer_renamed, inner).unwrap();

        assert!(alpha_equivalent(&arena, left, right));

        // NEGATIVE: keeping the inner quantifier is not the dual.
        let wrong_inner = arena.exists(inner_renamed, not_rab).unwrap();
        let wrong = arena.exists(outer_renamed, wrong_inner).unwrap();
        assert!(!alpha_equivalent(&arena, left, wrong));
    }

    /// NEGATIVE. Swapping the quantifier is not enough — the body must also be
    /// negated. `forall x. P x` is not the negation of `exists y. P y`.
    #[test]
    fn swapped_quantifier_with_unnegated_body_is_rejected() {
        let mut f = Fixture::new();
        let (x, y) = (f.binder(), f.binder());
        let px = f.p_of(x);
        let py = f.p_of(y);
        let universal = f.arena.forall(x, px).unwrap();
        let existential = f.arena.exists(y, py).unwrap();
        assert!(!alpha_equivalent_to_negation(
            &f.arena,
            universal,
            existential
        ));
    }

    /// NEGATIVE. The binder correspondence still applies at odd parity: the
    /// dual of `not (forall x. P x)` is `exists y. not (P y)`, not
    /// `exists y. not (P x)` (which leaves `x` free).
    #[test]
    fn duality_does_not_ignore_the_binder_correspondence() {
        let mut f = Fixture::new();
        let (x, y) = (f.binder(), f.binder());
        let px = f.p_of(x);
        let universal = f.arena.forall(x, px).unwrap();
        let negated_universal = f.arena.not(universal).unwrap();
        let not_px = f.arena.not(px).unwrap();
        let wrong_body = f.arena.exists(y, not_px).unwrap();
        assert!(!alpha_equivalent_to_negation(
            &f.arena,
            negated_universal,
            wrong_body
        ));
    }

    /// NEGATIVE. Propositional structure is not admitted at odd parity, even
    /// where a de Morgan identity would justify it. Declining is sound;
    /// guessing is not.
    #[test]
    fn propositional_structure_declines_at_odd_parity() {
        let mut arena = TermArena::new();
        let p = arena.declare("p", Sort::Bool).unwrap();
        let q = arena.declare("q", Sort::Bool).unwrap();
        let (pv, qv) = (arena.var(p), arena.var(q));
        let conjunction = arena.and(pv, qv).unwrap();
        let not_p = arena.not(pv).unwrap();
        let not_q = arena.not(qv).unwrap();
        let disjunction = arena.or(not_p, not_q).unwrap();
        // `not (p and q)` really *is* `(not p) or (not q)`, but this predicate
        // does not do propositional reasoning and must say so by declining.
        assert!(!alpha_equivalent_to_negation(
            &arena,
            conjunction,
            disjunction
        ));
    }

    /// The Boolean constants are each other's negation, and only that.
    #[test]
    fn boolean_constants_negate_each_other() {
        let mut arena = TermArena::new();
        let t = arena.bool_const(true);
        let f = arena.bool_const(false);
        assert!(alpha_equivalent_to_negation(&arena, t, f));
        assert!(alpha_equivalent_to_negation(&arena, f, t));
        assert!(!alpha_equivalent_to_negation(&arena, t, t));
        assert!(!alpha_equivalent_to_negation(&arena, f, f));
    }

    /// Doubled negations return to even parity rather than accumulating.
    #[test]
    fn double_negation_returns_to_even_parity() {
        let mut f = Fixture::new();
        let x = f.binder();
        let px = f.p_of(x);
        let not_px = f.arena.not(px).unwrap();
        let not_not_px = f.arena.not(not_px).unwrap();
        assert!(alpha_equivalent(&f.arena, not_not_px, px));
        assert!(!alpha_equivalent_to_negation(&f.arena, not_not_px, px));
        assert!(alpha_equivalent_to_negation(&f.arena, not_not_px, not_px));
    }

    /// NEGATIVE. Binder sorts are checked at odd parity too.
    #[test]
    fn duality_checks_binder_sorts() {
        let mut arena = TermArena::new();
        let narrow = arena.declare("n", Sort::BitVec(4)).unwrap();
        let wide = arena.declare("w", Sort::BitVec(8)).unwrap();
        let narrow_var = arena.var(narrow);
        let wide_var = arena.var(wide);
        let narrow_body = arena.eq(narrow_var, narrow_var).unwrap();
        let wide_body = arena.eq(wide_var, wide_var).unwrap();
        let not_wide_body = arena.not(wide_body).unwrap();
        let universal = arena.forall(narrow, narrow_body).unwrap();
        let negated = arena.not(universal).unwrap();
        let dual = arena.exists(wide, not_wide_body).unwrap();
        assert!(!alpha_equivalent_to_negation(&arena, negated, dual));
    }

    /// NEGATIVE, and a bug this actually had: a right-hand side that **shadows**
    /// a binder the left-hand side does not.
    ///
    /// ```text
    /// left  = forall x. forall z. R(x, z)      -- two distinct bound variables
    /// right = forall y. forall y. R(y, y)      -- one, shadowed; the outer is vacuous
    /// ```
    ///
    /// `left` demands `R` on every pair; `right` collapses to
    /// `forall y. R(y, y)` and demands it only on the diagonal, so `left` is
    /// strictly the stronger of the two and they are not equivalent. A
    /// correspondence lookup that consults only the left symbol maps `x -> y`
    /// and `z -> y`, finds both argument positions satisfied, and wrongly
    /// accepts. Matching the binder *depths* on both sides is what rejects it.
    #[test]
    fn right_hand_shadowing_is_not_alpha_equivalent() {
        let mut arena = TermArena::new();
        let carrier = Sort::Uninterpreted(arena.declare_uninterpreted_sort("U"));
        let relation = arena
            .declare_fun("R", &[carrier, carrier], Sort::Bool)
            .unwrap();
        let outer = arena.declare("x", carrier).unwrap();
        let inner = arena.declare("z", carrier).unwrap();
        let shadowed = arena.declare("y", carrier).unwrap();

        let (xv, zv) = (arena.var(outer), arena.var(inner));
        let distinct = arena.apply(relation, &[xv, zv]).unwrap();
        let left = arena.forall(inner, distinct).unwrap();
        let left = arena.forall(outer, left).unwrap();

        let yv = arena.var(shadowed);
        let diagonal = arena.apply(relation, &[yv, yv]).unwrap();
        let right = arena.forall(shadowed, diagonal).unwrap();
        let right = arena.forall(shadowed, right).unwrap();

        assert!(!alpha_equivalent(&arena, left, right));
        assert!(!alpha_equivalent(&arena, right, left));
    }

    /// The mirror of the above: the *left* side shadows and the right does not.
    #[test]
    fn left_hand_shadowing_is_not_alpha_equivalent() {
        let mut arena = TermArena::new();
        let carrier = Sort::Uninterpreted(arena.declare_uninterpreted_sort("U"));
        let relation = arena
            .declare_fun("R", &[carrier, carrier], Sort::Bool)
            .unwrap();
        let shadowed = arena.declare("x", carrier).unwrap();
        let outer = arena.declare("a", carrier).unwrap();
        let inner = arena.declare("b", carrier).unwrap();

        let xv = arena.var(shadowed);
        let diagonal = arena.apply(relation, &[xv, xv]).unwrap();
        let left = arena.forall(shadowed, diagonal).unwrap();
        let left = arena.forall(shadowed, left).unwrap();

        let (av, bv) = (arena.var(outer), arena.var(inner));
        let distinct = arena.apply(relation, &[av, bv]).unwrap();
        let right = arena.forall(inner, distinct).unwrap();
        let right = arena.forall(outer, right).unwrap();

        assert!(!alpha_equivalent(&arena, left, right));
    }

    /// Shadowing on *both* sides, consistently, still matches: the depths line
    /// up even though the names do not.
    #[test]
    fn matching_shadowing_on_both_sides_is_alpha_equivalent() {
        let mut arena = TermArena::new();
        let carrier = Sort::Uninterpreted(arena.declare_uninterpreted_sort("U"));
        let relation = arena
            .declare_fun("R", &[carrier, carrier], Sort::Bool)
            .unwrap();
        let left_name = arena.declare("x", carrier).unwrap();
        let right_name = arena.declare("y", carrier).unwrap();

        let xv = arena.var(left_name);
        let left_body = arena.apply(relation, &[xv, xv]).unwrap();
        let left = arena.forall(left_name, left_body).unwrap();
        let left = arena.forall(left_name, left).unwrap();

        let yv = arena.var(right_name);
        let right_body = arena.apply(relation, &[yv, yv]).unwrap();
        let right = arena.forall(right_name, right_body).unwrap();
        let right = arena.forall(right_name, right).unwrap();

        assert!(alpha_equivalent(&arena, left, right));
    }

    /// Quantifier-free terms fall back to plain structural equality.
    #[test]
    fn quantifier_free_terms_compare_structurally() {
        let mut arena = TermArena::new();
        let a = arena.bv_var("a", 8).unwrap();
        let b = arena.bv_var("b", 8).unwrap();
        let aa = arena.bv_add(a, a).unwrap();
        let ab = arena.bv_add(a, b).unwrap();
        assert!(alpha_equivalent(&arena, aa, aa));
        assert!(!alpha_equivalent(&arena, aa, ab));
    }
}
