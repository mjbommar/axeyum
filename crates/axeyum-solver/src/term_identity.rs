//! Small checked term-identity refutations.
//!
//! This module recognizes asserted disequalities whose two sides are equal after
//! a tiny, local identity normalization. It is deliberately narrow and
//! re-checkable: callers use the certificate only after the matcher re-scans the
//! original assertions.

use std::collections::{HashMap, HashSet};

use axeyum_ir::{Op, TermArena, TermId, TermNode};

use crate::term_walk::collect_top_binary_conjuncts as collect_top_conjuncts;

/// The checked identity class used by a term-identity refutation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TermIdentityKind {
    /// The asserted disequality is literally `not (= t t)`.
    Reflexive,
    /// The two sides coincide after constant-condition/equal-branch `ite`
    /// simplification.
    IteSimplification,
}

/// A self-checking refutation of `not (= lhs rhs)` where `lhs` and `rhs` are
/// identical under [`TermIdentityKind`]'s tiny identity normalizer.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct TermIdentityRefutationCertificate {
    /// The original top-level disequality assertion, or the conjunct containing
    /// it when the original assertion was a conjunction.
    pub assertion: TermId,
    /// The left side of the asserted equality inside the negation.
    pub lhs: TermId,
    /// The right side of the asserted equality inside the negation.
    pub rhs: TermId,
    /// Which identity class refutes the disequality.
    pub kind: TermIdentityKind,
}

/// Returns a certificate when any top-level conjunct is a disequality whose two
/// sides are equal by one of the checked term identities.
#[must_use]
pub fn term_identity_refutation(
    arena: &TermArena,
    assertions: &[TermId],
) -> Option<TermIdentityRefutationCertificate> {
    let mut conjuncts = Vec::new();
    for &assertion in assertions {
        collect_top_conjuncts(arena, assertion, &mut conjuncts);
    }

    // One memo for the whole scan. [`identity_normal_form`] is a pure function
    // of the term, so sharing the table across conjuncts is denotation-identical
    // and the second occurrence of a shared `ite` costs one lookup.
    let mut memo = NormalFormMemo::default();
    for assertion in conjuncts {
        let Some((lhs, rhs)) = match_disequality(arena, assertion) else {
            continue;
        };
        let Some(kind) = term_identity_kind(arena, lhs, rhs, &mut memo) else {
            continue;
        };
        return Some(TermIdentityRefutationCertificate {
            assertion,
            lhs,
            rhs,
            kind,
        });
    }
    None
}

fn match_disequality(arena: &TermArena, term: TermId) -> Option<(TermId, TermId)> {
    let TermNode::App {
        op: Op::BoolNot,
        args,
    } = arena.node(term)
    else {
        return None;
    };
    let [inner] = &**args else {
        return None;
    };
    let TermNode::App { op: Op::Eq, args } = arena.node(*inner) else {
        return None;
    };
    let [lhs, rhs] = &**args else {
        return None;
    };
    Some((*lhs, *rhs))
}

fn term_identity_kind(
    arena: &TermArena,
    lhs: TermId,
    rhs: TermId,
    memo: &mut NormalFormMemo,
) -> Option<TermIdentityKind> {
    if lhs == rhs {
        return Some(TermIdentityKind::Reflexive);
    }
    let (lhs_norm, lhs_changed) = identity_normal_form(arena, lhs, memo);
    let (rhs_norm, rhs_changed) = identity_normal_form(arena, rhs, memo);
    (lhs_norm == rhs_norm && (lhs_changed || rhs_changed))
        .then_some(TermIdentityKind::IteSimplification)
}

/// The answer [`identity_normal_form`] has already computed for a term, plus
/// the set of terms whose expansion has been scheduled.
///
/// # Why this exists
///
/// `identity_normal_form` descends BOTH branches of every non-constant `ite`.
/// Assertions are a shared DAG — an SMT-LIB `let` makes one `ite` reachable
/// from many parents, and `nec-smt`'s `prp-*` family nests thousands of them —
/// so the recursive form re-derived each shared node once per PATH, which is
/// exponential in the nesting depth rather than linear in the DAG.
///
/// That alone would be a performance note. What made it a division-sized
/// defect is *where* the walk sits: [`term_identity_refutation`] is the second
/// rung of `check_auto`'s dispatch, it takes **no deadline**, and it records no
/// route attempt — so a query that entered it never left, and the watchdog kill
/// that followed reported `attempts=2` with an empty phase stack. Measured
/// 2026-09-12 on
/// `QF_LIA/nec-smt/large/checkpass_pwd/prp-17-34.smt2` at a 24 s budget: a
/// `perf` profile put **99.81 %** of the run in `identity_normal_form`, and the
/// file's whole 24.9 s open segment was inside it.
///
/// Memoising is denotation-identical: the function is a pure function of the
/// term, so the table only removes repeated derivations of the same answer.
#[derive(Default)]
struct NormalFormMemo {
    /// Terms whose normal form is known.
    done: HashMap<TermId, (TermId, bool)>,
    /// Terms already expanded once, so a second parent does not re-expand them.
    scheduled: HashSet<TermId>,
}

/// One step of the explicit worklist that replaces the old native recursion.
///
/// Iterative rather than recursive for the reason `term_walk`'s spine walkers
/// are: the nesting depth is the *source's*, so a generator that emits a
/// thousand-deep `ite` chain used to decide how many stack frames the solver
/// took, and a stack overflow aborts the process instead of yielding a
/// first-class `unknown`.
enum Step {
    /// Expand this term (push its `Finish` marker and its children).
    Visit(TermId),
    /// Both children are resolved; combine them into this term's answer.
    Finish(TermId),
}

/// The `ite` operands of `term`, when it is a ternary `ite` — the only shape
/// this normalizer rewrites.
fn ite_operands(arena: &TermArena, term: TermId) -> Option<(TermId, TermId, TermId)> {
    let TermNode::App { op: Op::Ite, args } = arena.node(term) else {
        return None;
    };
    let [condition, then_term, else_term] = &**args else {
        return None;
    };
    Some((*condition, *then_term, *else_term))
}

fn identity_normal_form(
    arena: &TermArena,
    root: TermId,
    memo: &mut NormalFormMemo,
) -> (TermId, bool) {
    let mut work = vec![Step::Visit(root)];
    while let Some(step) = work.pop() {
        match step {
            Step::Visit(term) => {
                if memo.done.contains_key(&term) || !memo.scheduled.insert(term) {
                    continue;
                }
                let Some((condition, then_term, else_term)) = ite_operands(arena, term) else {
                    memo.done.insert(term, (term, false));
                    continue;
                };
                work.push(Step::Finish(term));
                match arena.node(condition) {
                    TermNode::BoolConst(true) => work.push(Step::Visit(then_term)),
                    TermNode::BoolConst(false) => work.push(Step::Visit(else_term)),
                    _ => {
                        work.push(Step::Visit(then_term));
                        work.push(Step::Visit(else_term));
                    }
                }
            }
            Step::Finish(term) => {
                let Some((condition, then_term, else_term)) = ite_operands(arena, term) else {
                    // Unreachable: only an `ite` is ever given a `Finish`.
                    memo.done.insert(term, (term, false));
                    continue;
                };
                // A missing child answer is impossible on a DAG (a child whose
                // `Finish` is still pending would have to be an ancestor), and
                // the fallback is the CONSERVATIVE one — "unchanged" can only
                // lose a refutation, never assert one.
                let child = |memo: &NormalFormMemo, t: TermId| {
                    memo.done.get(&t).copied().unwrap_or((t, false))
                };
                let value = match arena.node(condition) {
                    TermNode::BoolConst(true) => (child(memo, then_term).0, true),
                    TermNode::BoolConst(false) => (child(memo, else_term).0, true),
                    _ => {
                        let (then_norm, then_changed) = child(memo, then_term);
                        let (else_norm, else_changed) = child(memo, else_term);
                        if then_norm == else_norm {
                            (then_norm, true)
                        } else {
                            (term, then_changed || else_changed)
                        }
                    }
                };
                memo.done.insert(term, value);
            }
        }
    }
    memo.done.get(&root).copied().unwrap_or((root, false))
}

#[cfg(test)]
mod tests {
    use axeyum_ir::{Sort, TermArena};

    use super::{TermIdentityKind, term_identity_refutation};

    #[test]
    fn recognizes_ite_true_identity_disequality() {
        let mut arena = TermArena::new();
        let x = arena.real_var("x").unwrap();
        let y = arena.real_var("y").unwrap();
        let true_ = arena.bool_const(true);
        let ite = arena.ite(true_, x, y).unwrap();
        let eq = arena.eq(x, ite).unwrap();
        let diseq = arena.not(eq).unwrap();

        let cert = term_identity_refutation(&arena, &[diseq]).expect("ite true identity refutes");
        assert_eq!(cert.lhs, x);
        assert_eq!(cert.rhs, ite);
        assert_eq!(cert.kind, TermIdentityKind::IteSimplification);
    }

    #[test]
    fn rejects_nonconstant_distinct_ite_branches() {
        let mut arena = TermArena::new();
        let c = {
            let symbol = arena.declare("c", Sort::Bool).unwrap();
            arena.var(symbol)
        };
        let x = arena.real_var("x").unwrap();
        let y = arena.real_var("y").unwrap();
        let ite = arena.ite(c, x, y).unwrap();
        let eq = arena.eq(x, ite).unwrap();
        let diseq = arena.not(eq).unwrap();

        assert!(term_identity_refutation(&arena, &[diseq]).is_none());
    }

    /// The defect this module's memo exists for, as a test that FAILS by not
    /// finishing rather than by asserting.
    ///
    /// Each level is `ite(c, t, t)` over the level below, so the recursive
    /// normalizer descended both branches of the SAME shared node and did
    /// `2^depth` work on a DAG of `depth` nodes. At 64 levels that is 1.8e19
    /// derivations — the pre-memo form does not return in any budget, which is
    /// exactly how `prp-17-34.smt2` spent 24.9 s of a 24 s budget inside
    /// `identity_normal_form` with no route attempt recorded.
    ///
    /// It is also a value assertion, not only a liveness one: every level has
    /// equal branches, so the whole chain normalizes to `x` and the disequality
    /// `not (= x t_64)` is refuted by `IteSimplification`.
    #[test]
    fn a_shared_ite_chain_normalizes_in_dag_size_not_path_count() {
        let mut arena = TermArena::new();
        let x = arena.real_var("x").unwrap();
        let c = {
            let symbol = arena.declare("c", Sort::Bool).unwrap();
            arena.var(symbol)
        };
        let mut level = x;
        for _ in 0..64 {
            level = arena.ite(c, level, level).unwrap();
        }
        // Non-vacuity: the chain must still BE an `ite` DAG. If the arena ever
        // folds `ite(c, t, t)` at construction this test would silently become
        // a test of `x` against itself.
        assert!(
            matches!(
                arena.node(level),
                axeyum_ir::TermNode::App {
                    op: axeyum_ir::Op::Ite,
                    ..
                }
            ),
            "the chain collapsed at construction; this test no longer covers the walk"
        );
        assert_ne!(level, x, "the chain must not be the bare variable");

        let eq = arena.eq(x, level).unwrap();
        let diseq = arena.not(eq).unwrap();
        let cert = term_identity_refutation(&arena, &[diseq])
            .expect("equal branches at every level normalize the chain to x");
        assert_eq!(cert.kind, TermIdentityKind::IteSimplification);
        assert_eq!(cert.lhs, x);
        assert_eq!(cert.rhs, level);
    }

    /// The memo must not manufacture a refutation on the same shape: a chain
    /// whose branches genuinely differ stays unrefuted however deeply shared.
    #[test]
    fn a_shared_ite_chain_with_distinct_branches_is_not_refuted() {
        let mut arena = TermArena::new();
        let x = arena.real_var("x").unwrap();
        let y = arena.real_var("y").unwrap();
        let c = {
            let symbol = arena.declare("c", Sort::Bool).unwrap();
            arena.var(symbol)
        };
        let mut then_level = x;
        let mut else_level = y;
        for _ in 0..64 {
            let next_then = arena.ite(c, then_level, else_level).unwrap();
            let next_else = arena.ite(c, else_level, then_level).unwrap();
            then_level = next_then;
            else_level = next_else;
        }
        let eq = arena.eq(then_level, else_level).unwrap();
        let diseq = arena.not(eq).unwrap();
        assert!(term_identity_refutation(&arena, &[diseq]).is_none());
    }
}
