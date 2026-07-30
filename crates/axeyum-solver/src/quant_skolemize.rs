//! Polarity-aware **NNF + Skolemization + prenexing**, so trigger instantiation
//! can reach quantifiers that are nested rather than only top level.
//!
//! # Why this exists
//!
//! Trigger instantiation only ever saw *top-level* universals. Anything else — an
//! `exists` in positive position, a `forall` under a `not` or under a connective —
//! left a residual quantifier and the query was declined `Incomplete` before
//! search began.
//!
//! That is the single largest measured gap in the UF division. Over a 300-file UF
//! slice, **126 of the 159 files carrying a declared status** (83 % of the
//! residual) declined for exactly this reason, against **3** files in the
//! saturated-but-unproven state that better instance *selection* would serve. Of
//! those 126, **109 have an `exists` nested under a `forall`**, which is why this
//! pass emits Skolem **functions** over the enclosing universal variables and not
//! only the constants [`crate::auto`]'s `skolemize_top_existentials` already
//! produced — constants cover at most 29 of them and are the arity-0 case here.
//!
//! # Why all three steps are needed together
//!
//! Skolemization alone was measured **insufficient**: it fired on these files
//! (`changed = true`) and instantiation still reported a residual quantifier,
//! because discharging the existentials leaves the *universals* exactly where
//! they were — nested under connectives, still out of reach. So the pass also
//! converts to NNF and **hoists the surviving universals to the front**.
//!
//! `walk(t, positive)` returns the NNF of `t` when `positive`, and of `¬t`
//! otherwise, which pushes negation to the leaves and lets every quantifier be
//! read at its true force:
//!
//! - `exists x. φ` positive and `forall x. φ` negative are **existential in
//!   force**: `x` becomes `sk(u₁ … uₙ)` over the enclosing universals and the
//!   quantifier is dropped.
//! - `forall x. φ` positive and `exists x. φ` negative are **universal in
//!   force**: `x` is renamed to a fresh symbol, recorded, and the quantifier node
//!   is dropped so it can be re-attached at the very front.
//!
//! Every hoisted variable is renamed, which is what makes hoisting out of a
//! disjunction sound: `(∀x. A(x)) ∨ B ≡ ∀x. (A(x) ∨ B)` requires `x` not free in
//! `B`, and freshness guarantees it. It also keeps two branches that happened to
//! reuse one bound symbol from being conflated into a single top-level variable.
//!
//! # Where it deliberately gives up
//!
//! Under `BoolXor`, `Eq` on `Bool`, and `Ite`, a subterm sits in **both**
//! polarities at once, so it has no NNF in this sense and no single Skolem choice
//! is valid. If a quantifier occurs under one of those, the pass abandons that
//! assertion and returns it untouched; the caller then declines exactly as it did
//! before. Being wrong here would not be a missed refutation — it would be an
//! unsound one.
//!
//! # Soundness
//!
//! Skolemization preserves **satisfiability**, not logical equivalence, so this
//! is sound in the refutation direction only: if the transformed query is
//! `unsat`, the original is `unsat`. A `sat` verdict does **not** transfer, since
//! the model interprets Skolem symbols the original query does not contain and
//! so could not be replayed against it — and this project requires every `sat` to
//! replay against the original term. [`skolemize_assertions`] reports whether it
//! changed anything, and a caller acting on the result must not return a bare
//! `sat` from it.
//!
//! Symbols are declared through `declare_internal*` under reserved `!qsk`/
//! `!qskf`/`!qu` prefixes, distinct from the `!sk` used by
//! `auto::skolemize_top_existentials` so the two skolemizers cannot interfere,
//! and each name is probed for freshness (see `fresh_name`) so the output stays
//! deterministic without ever reusing a symbol.

use std::collections::HashMap;

use axeyum_ir::{Op, Sort, SymbolId, TermArena, TermId, TermNode};

use crate::backend::SolverError;

/// Result of [`skolemize_assertions`].
pub(crate) struct Skolemized {
    /// The rewritten assertions, in input order.
    pub(crate) assertions: Vec<TermId>,
    /// Whether any quantifier was actually moved or discharged. When `false` the
    /// assertions are unchanged and callers should keep their previous route.
    pub(crate) changed: bool,
}

/// Rewrites `assertions` to NNF, Skolemizes every existential-in-force
/// quantifier, and hoists the surviving universals to the front of each
/// assertion.
///
/// See the module docs for the polarity rules, the deliberate bail-outs, and why
/// the result is sound for refutation only.
///
/// # Errors
///
/// Returns [`SolverError::Backend`] if declaring a symbol or rebuilding a term
/// fails in the arena.
pub(crate) fn skolemize_assertions(
    arena: &mut TermArena,
    assertions: &[TermId],
) -> Result<Skolemized, SolverError> {
    let mut state = SkolemState {
        next: 0,
        changed: false,
        bailed: false,
    };
    let mut out = Vec::with_capacity(assertions.len());
    for &assertion in assertions {
        let before = state.changed;
        let mut universals = Vec::new();
        let mut subst = HashMap::new();
        state.bailed = false;
        let rewritten = state.walk(
            arena,
            assertion,
            true,
            &mut Vec::new(),
            &mut subst,
            &mut universals,
        )?;
        if state.bailed {
            // A quantifier under a polarity-mixing operator: leave this assertion
            // exactly as it was rather than guess a witness.
            state.changed = before;
            out.push(assertion);
            continue;
        }
        // Re-attach the hoisted universals at the front, innermost last so the
        // original nesting order is preserved.
        let mut wrapped = rewritten;
        for &symbol in universals.iter().rev() {
            wrapped = arena
                .forall(symbol, wrapped)
                .map_err(|e| SolverError::Backend(e.to_string()))?;
        }
        out.push(wrapped);
    }
    Ok(Skolemized {
        assertions: out,
        changed: state.changed,
    })
}

struct SkolemState {
    next: u32,
    changed: bool,
    bailed: bool,
}

impl SkolemState {
    /// Returns the NNF of `term` when `positive`, and of `¬term` otherwise.
    ///
    /// `enclosing` are the (renamed) universal variables in scope, which any
    /// Skolem function created below depends on; `subst` maps original bound
    /// symbols to their replacements; `hoisted` collects every renamed universal
    /// for re-attachment at the front of the assertion.
    fn walk(
        &mut self,
        arena: &mut TermArena,
        term: TermId,
        positive: bool,
        enclosing: &mut Vec<SymbolId>,
        subst: &mut HashMap<SymbolId, TermId>,
        hoisted: &mut Vec<SymbolId>,
    ) -> Result<TermId, SolverError> {
        let err = |e: axeyum_ir::IrError| SolverError::Backend(e.to_string());
        if self.bailed {
            return Ok(term);
        }
        let node = arena.node(term).clone();
        let TermNode::App { op, args } = node else {
            return Self::leaf(arena, term, positive, subst);
        };

        match op {
            Op::BoolNot => self.walk(arena, args[0], !positive, enclosing, subst, hoisted),
            Op::BoolImplies => {
                // `a => b` is `¬a ∨ b`, so the antecedent carries flipped polarity
                // and the whole node dualizes under negation.
                let left = self.walk(arena, args[0], !positive, enclosing, subst, hoisted)?;
                let right = self.walk(arena, args[1], positive, enclosing, subst, hoisted)?;
                if positive {
                    arena.or(left, right).map_err(err)
                } else {
                    arena.and(left, right).map_err(err)
                }
            }
            Op::BoolAnd | Op::BoolOr => {
                let mut rebuilt = Vec::with_capacity(args.len());
                for &arg in &args {
                    rebuilt.push(self.walk(arena, arg, positive, enclosing, subst, hoisted)?);
                }
                // De Morgan: the connective flips when the polarity is negative.
                let conjunction = matches!(op, Op::BoolAnd) == positive;
                let mut folded = rebuilt[0];
                for &next in &rebuilt[1..] {
                    folded = if conjunction {
                        arena.and(folded, next).map_err(err)?
                    } else {
                        arena.or(folded, next).map_err(err)?
                    };
                }
                Ok(folded)
            }
            Op::Forall(symbol) if positive => {
                self.hoist_universal(arena, symbol, args[0], positive, enclosing, subst, hoisted)
            }
            Op::Exists(symbol) if !positive => {
                self.hoist_universal(arena, symbol, args[0], positive, enclosing, subst, hoisted)
            }
            Op::Exists(symbol) | Op::Forall(symbol) => {
                let sort = arena.symbol(symbol).1;
                let witness = self.fresh_skolem(arena, sort, enclosing)?;
                let shadowed = subst.insert(symbol, witness);
                let body = self.walk(arena, args[0], positive, enclosing, subst, hoisted)?;
                Self::restore(subst, symbol, shadowed);
                self.changed = true;
                Ok(body)
            }
            // Polarity-mixing operators put a subterm in both polarities at once,
            // so they have no NNF as written. When a quantifier is under one, they
            // are expanded into their polarity-pure equivalent first; the copies
            // are then walked independently and each existential occurrence gets
            // its own witness, which is exactly standard NNF. The expansion is
            // gated on actually containing a quantifier so quantifier-free terms
            // are never duplicated.
            Op::BoolXor if contains_quantifier(arena, term) => {
                // a xor b  ≡  (a ∨ b) ∧ (¬a ∨ ¬b)
                let (a, b) = (args[0], args[1]);
                let not_a = arena.not(a).map_err(err)?;
                let not_b = arena.not(b).map_err(err)?;
                let either = arena.or(a, b).map_err(err)?;
                let not_both = arena.or(not_a, not_b).map_err(err)?;
                let expanded = arena.and(either, not_both).map_err(err)?;
                self.walk(arena, expanded, positive, enclosing, subst, hoisted)
            }
            Op::Eq if arena.sort_of(args[0]) == Sort::Bool && contains_quantifier(arena, term) => {
                // a = b  ≡  (a ⇒ b) ∧ (b ⇒ a)
                let (a, b) = (args[0], args[1]);
                let forward = arena.implies(a, b).map_err(err)?;
                let backward = arena.implies(b, a).map_err(err)?;
                let expanded = arena.and(forward, backward).map_err(err)?;
                self.walk(arena, expanded, positive, enclosing, subst, hoisted)
            }
            Op::Ite if arena.sort_of(term) == Sort::Bool && contains_quantifier(arena, term) => {
                // ite(c, a, b)  ≡  (c ⇒ a) ∧ (¬c ⇒ b)
                let (c, a, b) = (args[0], args[1], args[2]);
                let not_c = arena.not(c).map_err(err)?;
                let then_branch = arena.implies(c, a).map_err(err)?;
                let else_branch = arena.implies(not_c, b).map_err(err)?;
                let expanded = arena.and(then_branch, else_branch).map_err(err)?;
                self.walk(arena, expanded, positive, enclosing, subst, hoisted)
            }
            _ => {
                // A quantifier under a *non-Bool* mixing position (e.g. an `ite`
                // whose branches are terms, or an equality between non-Bool sorts)
                // has no such expansion. Leave the assertion alone rather than
                // guess a witness: being wrong here would be an unsound
                // refutation, not a missed one.
                if contains_quantifier(arena, term) {
                    self.bailed = true;
                    return Ok(term);
                }
                Self::leaf(arena, term, positive, subst)
            }
        }
    }

    /// Renames a universal-in-force variable, records it for hoisting, and drops
    /// the quantifier node.
    #[allow(clippy::too_many_arguments)]
    fn hoist_universal(
        &mut self,
        arena: &mut TermArena,
        symbol: SymbolId,
        body: TermId,
        positive: bool,
        enclosing: &mut Vec<SymbolId>,
        subst: &mut HashMap<SymbolId, TermId>,
        hoisted: &mut Vec<SymbolId>,
    ) -> Result<TermId, SolverError> {
        let err = |e: axeyum_ir::IrError| SolverError::Backend(e.to_string());
        let sort = arena.symbol(symbol).1;
        // Fresh name: hoisting out of a disjunction is only sound when the
        // variable is not free in the other branch, and this guarantees it.
        let name = self.fresh_name(arena, "!qu_");
        let renamed = arena.declare_internal(&name, sort).map_err(err)?;
        let replacement = arena.var(renamed);
        let shadowed = subst.insert(symbol, replacement);
        enclosing.push(renamed);
        hoisted.push(renamed);
        let rewritten = self.walk(arena, body, positive, enclosing, subst, hoisted);
        enclosing.pop();
        Self::restore(subst, symbol, shadowed);
        self.changed = true;
        rewritten
    }

    /// A name of the form `<prefix><n>` that is not yet present in the arena.
    ///
    /// The counter alone is not enough: it restarts on every call while
    /// `declare_internal` persists for the life of the arena, so a second run
    /// over the same arena would reuse `!sk_3` — either colliding with a
    /// different sort (a hard error, observed on
    /// `sledgehammer__Fundamental_Theorem_Algebra__uf.1106692.smt2`) or, worse,
    /// silently succeeding and making two unrelated existentials share one
    /// witness. Probing keeps the choice deterministic: it depends only on the
    /// arena contents and the traversal order.
    ///
    /// The probe must consult the **internal** namespace. `find_symbol` only sees
    /// user-declared names and is blind to everything `declare_internal` minted,
    /// so probing with it reports "free" every time and defeats the check. Both
    /// the symbol and function tables are checked because this prefix pool feeds
    /// `declare_internal` and `declare_internal_fun` alike.
    fn fresh_name(&mut self, arena: &TermArena, prefix: &str) -> String {
        loop {
            let candidate = format!("{prefix}{}", self.next);
            self.next += 1;
            if arena.find_internal_symbol(&candidate).is_none()
                && arena.find_internal_function(&candidate).is_none()
            {
                return candidate;
            }
        }
    }

    /// A fresh Skolem term of `sort`: a constant when nothing encloses it,
    /// otherwise an application over the enclosing universal variables.
    fn fresh_skolem(
        &mut self,
        arena: &mut TermArena,
        sort: Sort,
        enclosing: &[SymbolId],
    ) -> Result<TermId, SolverError> {
        let err = |e: axeyum_ir::IrError| SolverError::Backend(e.to_string());
        if enclosing.is_empty() {
            let name = self.fresh_name(arena, "!qsk_");
            let symbol = arena.declare_internal(&name, sort).map_err(err)?;
            return Ok(arena.var(symbol));
        }
        let params: Vec<Sort> = enclosing.iter().map(|&s| arena.symbol(s).1).collect();
        let name = self.fresh_name(arena, "!qskf_");
        let func = arena
            .declare_internal_fun(&name, &params, sort)
            .map_err(err)?;
        let args: Vec<TermId> = enclosing.iter().map(|&s| arena.var(s)).collect();
        arena.apply(func, &args).map_err(err)
    }

    /// A quantifier-free leaf: apply the pending substitution, and negate it when
    /// the polarity is negative (NNF pushes negation this far and no further).
    fn leaf(
        arena: &mut TermArena,
        term: TermId,
        positive: bool,
        subst: &HashMap<SymbolId, TermId>,
    ) -> Result<TermId, SolverError> {
        let err = |e: axeyum_ir::IrError| SolverError::Backend(e.to_string());
        let mut rewritten = term;
        if !subst.is_empty() {
            let map: HashMap<TermId, TermId> = subst
                .iter()
                .map(|(&symbol, &replacement)| (arena.var(symbol), replacement))
                .collect();
            let mut memo = HashMap::new();
            rewritten =
                axeyum_rewrite::replace_subterms(arena, term, &map, &mut memo).map_err(err)?;
        }
        if positive {
            Ok(rewritten)
        } else {
            arena.not(rewritten).map_err(err)
        }
    }

    fn restore(subst: &mut HashMap<SymbolId, TermId>, symbol: SymbolId, shadowed: Option<TermId>) {
        match shadowed {
            Some(previous) => {
                subst.insert(symbol, previous);
            }
            None => {
                subst.remove(&symbol);
            }
        }
    }
}

/// Whether any quantifier occurs anywhere in `term`.
fn contains_quantifier(arena: &TermArena, term: TermId) -> bool {
    let mut stack = vec![term];
    let mut seen = std::collections::HashSet::new();
    while let Some(current) = stack.pop() {
        if !seen.insert(current) {
            continue;
        }
        if let TermNode::App { op, args } = arena.node(current) {
            if matches!(op, Op::Forall(_) | Op::Exists(_)) {
                return true;
            }
            stack.extend(args.iter().copied());
        }
    }
    false
}

#[cfg(test)]
mod tests {
    use super::*;
    use axeyum_ir::Sort;

    /// Counts quantifier nodes reachable from `term`.
    fn quantifiers(arena: &TermArena, term: TermId) -> usize {
        let mut stack = vec![term];
        let mut seen = std::collections::HashSet::new();
        let mut count = 0;
        while let Some(current) = stack.pop() {
            if !seen.insert(current) {
                continue;
            }
            if let TermNode::App { op, args } = arena.node(current) {
                if matches!(op, Op::Forall(_) | Op::Exists(_)) {
                    count += 1;
                }
                stack.extend(args.iter().copied());
            }
        }
        count
    }

    fn has_skolem_application(arena: &TermArena, term: TermId) -> bool {
        let mut stack = vec![term];
        let mut seen = std::collections::HashSet::new();
        while let Some(current) = stack.pop() {
            if !seen.insert(current) {
                continue;
            }
            if let TermNode::App { op, args } = arena.node(current) {
                if matches!(op, Op::Apply(_)) {
                    return true;
                }
                stack.extend(args.iter().copied());
            }
        }
        false
    }

    #[test]
    fn positive_top_level_exists_becomes_a_skolem_constant() {
        let mut arena = TermArena::new();
        let x = arena.declare("x", Sort::Bool).unwrap();
        let body = arena.var(x);
        let assertion = arena.exists(x, body).unwrap();

        let out = skolemize_assertions(&mut arena, &[assertion]).unwrap();

        assert!(out.changed);
        assert_eq!(quantifiers(&arena, out.assertions[0]), 0);
        // No enclosing universal, so the witness is a constant, not an application.
        assert!(!has_skolem_application(&arena, out.assertions[0]));
    }

    #[test]
    fn exists_under_forall_becomes_a_skolem_function_of_that_universal() {
        // `forall u. exists e. (u = e)` — the shape behind 109 of the 126 blocked
        // UF files, and the reason constants alone are not enough.
        let mut arena = TermArena::new();
        let u = arena.declare("u", Sort::Int).unwrap();
        let e = arena.declare("e", Sort::Int).unwrap();
        let (uv, ev) = (arena.var(u), arena.var(e));
        let body = arena.eq(uv, ev).unwrap();
        let inner = arena.exists(e, body).unwrap();
        let assertion = arena.forall(u, inner).unwrap();

        let out = skolemize_assertions(&mut arena, &[assertion]).unwrap();

        assert!(out.changed);
        // The universal survives; only the existential is discharged.
        assert_eq!(quantifiers(&arena, out.assertions[0]), 1);
        assert!(
            has_skolem_application(&arena, out.assertions[0]),
            "the witness must depend on the enclosing universal"
        );
    }

    #[test]
    fn negative_forall_is_existential_in_force_and_is_skolemized() {
        let mut arena = TermArena::new();
        let x = arena.declare("x", Sort::Bool).unwrap();
        let body = arena.var(x);
        let inner = arena.forall(x, body).unwrap();
        let assertion = arena.not(inner).unwrap();

        let out = skolemize_assertions(&mut arena, &[assertion]).unwrap();

        assert!(out.changed);
        assert_eq!(quantifiers(&arena, out.assertions[0]), 0);
    }

    #[test]
    fn negative_exists_is_universal_in_force_and_is_kept() {
        let mut arena = TermArena::new();
        let x = arena.declare("x", Sort::Bool).unwrap();
        let body = arena.var(x);
        let inner = arena.exists(x, body).unwrap();
        let assertion = arena.not(inner).unwrap();

        let out = skolemize_assertions(&mut arena, &[assertion]).unwrap();

        // `¬∃x. φ` is `∀x. ¬φ`: universal in force, so it must survive as a
        // quantifier rather than be discharged to a witness.
        assert_eq!(quantifiers(&arena, out.assertions[0]), 1);
        assert!(
            matches!(
                arena.node(out.assertions[0]),
                TermNode::App {
                    op: Op::Forall(_),
                    ..
                }
            ),
            "NNF must surface it as a top-level forall"
        );
        assert!(!has_skolem_application(&arena, out.assertions[0]));
    }

    #[test]
    fn antecedent_of_an_implication_flips_polarity() {
        // `(forall x. p(x)) => q` puts the universal in negative position, where
        // it is existential in force.
        let mut arena = TermArena::new();
        let x = arena.declare("x", Sort::Bool).unwrap();
        let q = arena.declare("q", Sort::Bool).unwrap();
        let body = arena.var(x);
        let antecedent = arena.forall(x, body).unwrap();
        let consequent = arena.var(q);
        let assertion = arena.implies(antecedent, consequent).unwrap();

        let out = skolemize_assertions(&mut arena, &[assertion]).unwrap();

        assert!(out.changed);
        assert_eq!(quantifiers(&arena, out.assertions[0]), 0);
    }

    #[test]
    fn a_quantifier_under_xor_is_expanded_rather_than_abandoned() {
        // `xor` puts a subterm in both polarities, so it has no NNF as written.
        // Rather than give up, it is expanded to `(a ∨ b) ∧ (¬a ∨ ¬b)`, which is
        // polarity-pure. The existential then occurs once positively (a witness)
        // and once negatively (a universal), which is standard NNF.
        //
        // This matters: bailing out here left a residual quantifier, and a single
        // abandoned assertion is enough to make the whole query undecidable by
        // instantiation -- 7 such assertions in one file blocked all 379.
        let mut arena = TermArena::new();
        let x = arena.declare("x", Sort::Bool).unwrap();
        let q = arena.declare("q", Sort::Bool).unwrap();
        let body = arena.var(x);
        let inner = arena.exists(x, body).unwrap();
        let other = arena.var(q);
        let assertion = arena.xor(inner, other).unwrap();

        let out = skolemize_assertions(&mut arena, &[assertion]).unwrap();

        assert!(out.changed);
        // The negative occurrence survives as a universal; the positive one became
        // a witness, so exactly one binder remains.
        assert_eq!(quantifiers(&arena, out.assertions[0]), 1);
    }

    #[test]
    fn a_quantifier_under_a_non_bool_ite_is_left_alone() {
        // `ite(∃x. x, 1, 2)` is Int-sorted, so the Bool expansion does not apply
        // and there is no sound polarity to read the quantifier at. The assertion
        // must come back untouched rather than be given a guessed witness --
        // being wrong here would be an unsound refutation, not a missed one.
        let mut arena = TermArena::new();
        let x = arena.declare("x", Sort::Bool).unwrap();
        let body = arena.var(x);
        let condition = arena.exists(x, body).unwrap();
        let one = arena.int_const(1);
        let two = arena.int_const(2);
        let chosen = arena.ite(condition, one, two).unwrap();
        let assertion = arena.eq(chosen, one).unwrap();

        let out = skolemize_assertions(&mut arena, &[assertion]).unwrap();

        assert!(
            !out.changed,
            "a non-Bool mixing position must abandon the assertion"
        );
        assert_eq!(out.assertions[0], assertion);
        assert_eq!(quantifiers(&arena, out.assertions[0]), 1);
    }

    #[test]
    fn a_universal_under_a_connective_is_hoisted_to_the_front() {
        // The property Skolemization alone did NOT deliver. `q ∧ (forall x. p(x))`
        // has no top-level universal, so trigger instantiation could not see it;
        // after this pass the `forall` must be the outermost node.
        let mut arena = TermArena::new();
        let x = arena.declare("x", Sort::Bool).unwrap();
        let q = arena.declare("q", Sort::Bool).unwrap();
        let body = arena.var(x);
        let inner = arena.forall(x, body).unwrap();
        let other = arena.var(q);
        let assertion = arena.and(other, inner).unwrap();

        let out = skolemize_assertions(&mut arena, &[assertion]).unwrap();

        assert!(out.changed);
        assert!(
            matches!(
                arena.node(out.assertions[0]),
                TermNode::App {
                    op: Op::Forall(_),
                    ..
                }
            ),
            "the universal must be hoisted to the front, not left under the `and`"
        );
        assert_eq!(quantifiers(&arena, out.assertions[0]), 1);
    }

    #[test]
    fn two_branches_reusing_one_bound_symbol_do_not_share_a_hoisted_variable() {
        // Hoisting `(forall x. A) ∨ (forall x. B)` to a single `forall x` would
        // conflate two independent variables. Renaming is what makes hoisting out
        // of a disjunction sound.
        let mut arena = TermArena::new();
        let x = arena.declare("x", Sort::Bool).unwrap();
        let body = arena.var(x);
        let left = arena.forall(x, body).unwrap();
        let right = arena.forall(x, body).unwrap();
        let assertion = arena.or(left, right).unwrap();

        let out = skolemize_assertions(&mut arena, &[assertion]).unwrap();

        assert!(out.changed);
        // Both universals survive as distinct binders rather than collapsing.
        assert_eq!(quantifiers(&arena, out.assertions[0]), 2);
        let mut binders = Vec::new();
        let mut stack = vec![out.assertions[0]];
        while let Some(t) = stack.pop() {
            if let TermNode::App { op, args } = arena.node(t) {
                if let Op::Forall(sym) = op {
                    binders.push(*sym);
                }
                stack.extend(args.iter().copied());
            }
        }
        assert_ne!(binders[0], binders[1], "hoisted binders must be distinct");
    }

    #[test]
    fn a_quantifier_free_query_is_reported_unchanged() {
        let mut arena = TermArena::new();
        let q = arena.declare("q", Sort::Bool).unwrap();
        let assertion = arena.var(q);

        let out = skolemize_assertions(&mut arena, &[assertion]).unwrap();

        assert!(!out.changed);
        assert_eq!(out.assertions[0], assertion);
    }

    #[test]
    fn distinct_existentials_get_distinct_witnesses() {
        let mut arena = TermArena::new();
        let a = arena.declare("a", Sort::Bool).unwrap();
        let b = arena.declare("b", Sort::Bool).unwrap();
        let (av, bv) = (arena.var(a), arena.var(b));
        let first = arena.exists(a, av).unwrap();
        let second = arena.exists(b, bv).unwrap();

        let out = skolemize_assertions(&mut arena, &[first, second]).unwrap();

        assert!(out.changed);
        assert_ne!(
            out.assertions[0], out.assertions[1],
            "separate existentials must not share a witness"
        );
    }
}
