//! The ℤ fragment — the same rewrite-chain design as [`super::nat`], forced
//! into a NON-generic shape by the carrier
//! ([`crate::int_prelude::ops::IntDev`], mirroring [`crate::ring::int`]'s
//! own choice, ADR-1582): `IntDev`'s `Int`-typed combinators (`icongr`/
//! `itrans`/`isymm`/`ichain`/`ieq`) are inherent methods, not a trait, so
//! there is no `D: SomeIntOps` type parameter to be generic over.
//!
//! ## The default rule set
//!
//! Every unconditional identity/annihilator/defining law `IntPrelude`
//! carries with no side condition:
//!
//! | lemma | statement |
//! | --- | --- |
//! | `add_zero` | `add a zero = a` |
//! | `add_neg` | `add a (neg a) = zero` (repeated pattern variable) |
//! | `add_neg_cancel_right` | `add (add a b) (neg b) = a` |
//! | `add_neg_eq_sub` | `add a (neg b) = sub a b` |
//! | `mul_one` | `mul a one = a` |
//! | `one_mul` | `mul one a = a` |
//! | `neg_one_mul` | `mul (neg one) a = neg a` |
//! | `mul_zero` | `mul a zero = zero` |
//! | `neg_add` | `neg (add a b) = add (neg a) (neg b)` |
//! | `mul_neg` | `mul a (neg b) = neg (mul a b)` |
//!
//! **There is no `zero_add`/`zero_mul` in `IntPrelude`** (only the
//! `_zero`-suffixed forms exist) — a goal needing the reversed argument
//! order must route through `add_comm`/`mul_comm` as a caller-supplied
//! extra rule, exactly [`super::nat`]'s `distrib_one_plus` retirement did
//! for `right_distrib`. See [`with_extra`] and the module docs on rule
//! ordering below.
//!
//! ## A sharper termination hazard than ℕ's
//!
//! [`super::nat`]'s module docs explain why a bare commutativity law can
//! never be a DEFAULT (its pattern matches its own output). For ℤ the same
//! reasoning cuts a *narrower* set of extras than it might first appear:
//! `add_comm`/`mul_comm` are still safe to add as an EXTRA only when the
//! goal's post-annihilation fixed point has no `add`/`mul` structure left
//! for comm to keep re-swapping — e.g. `add_comm` then `add_neg` collapses
//! all the way to a bare `zero`, which has no further `App` structure at
//! all, so the run genuinely halts. A goal like `Eq (mul (neg a) b) (neg
//! (mul a b))` (`neg_mul`, NOT a target here) looks similar but its fixed
//! point still contains a bare `mul a b`/`mul b a` pair with nothing to
//! annihilate it, so `mul_comm` matches it FOREVER once added — that shape
//! was tried and discarded during this module's own retirement search,
//! confirmed by running it and observing [`Decline::BudgetExceeded`], not
//! by inspection alone. **Rule order is also load-bearing**: a default rule
//! must be checked before a commutativity extra at the same node so it wins
//! the match race the first time both apply — [`with_extra`] appends extras
//! after the defaults, which is what makes this automatic rather than a
//! caller obligation.

use crate::ExprNode;
use crate::IntPrelude;
use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::name::NameId;
use crate::nat_prelude::NatOps;

use super::{Decline, MAX_STEPS, Orientation};

/// One oriented rewrite rule over ℤ — see [`super::nat::Rule`]'s docs; the
/// only difference is the concrete, non-generic `IntDev` carrier.
#[derive(Clone, Copy)]
pub(crate) struct Rule {
    /// The declared lemma this rule cites.
    pub name: NameId,
    /// How many pattern variables `build` expects.
    pub arity: usize,
    /// Which side the pattern matches, and which way the rewrite runs.
    pub orientation: Orientation,
    /// `(lhs, rhs)` of the lemma's statement, over `arity` args.
    pub build: fn(&mut IntDev<'_>, &[ExprId]) -> (ExprId, ExprId),
}

fn r_add_zero(d: &mut IntDev<'_>, a: &[ExprId]) -> (ExprId, ExprId) {
    let z = d.izero();
    (d.iadd(a[0], z), a[0])
}
fn r_add_neg(d: &mut IntDev<'_>, a: &[ExprId]) -> (ExprId, ExprId) {
    let z = d.izero();
    let na = d.ineg(a[0]);
    (d.iadd(a[0], na), z)
}
fn r_add_neg_cancel_right(d: &mut IntDev<'_>, a: &[ExprId]) -> (ExprId, ExprId) {
    let ab = d.iadd(a[0], a[1]);
    let nb = d.ineg(a[1]);
    (d.iadd(ab, nb), a[0])
}
fn r_add_neg_eq_sub(d: &mut IntDev<'_>, a: &[ExprId]) -> (ExprId, ExprId) {
    let nb = d.ineg(a[1]);
    let lhs = d.iadd(a[0], nb);
    let rhs = d.isub(a[0], a[1]);
    (lhs, rhs)
}
fn r_mul_one(d: &mut IntDev<'_>, a: &[ExprId]) -> (ExprId, ExprId) {
    let one = d.ione();
    (d.imul(a[0], one), a[0])
}
fn r_one_mul(d: &mut IntDev<'_>, a: &[ExprId]) -> (ExprId, ExprId) {
    let one = d.ione();
    (d.imul(one, a[0]), a[0])
}
fn r_neg_one_mul(d: &mut IntDev<'_>, a: &[ExprId]) -> (ExprId, ExprId) {
    let one = d.ione();
    let neg_one = d.ineg(one);
    let lhs = d.imul(neg_one, a[0]);
    let rhs = d.ineg(a[0]);
    (lhs, rhs)
}
fn r_mul_zero(d: &mut IntDev<'_>, a: &[ExprId]) -> (ExprId, ExprId) {
    let z = d.izero();
    (d.imul(a[0], z), z)
}
fn r_neg_add(d: &mut IntDev<'_>, a: &[ExprId]) -> (ExprId, ExprId) {
    let ab = d.iadd(a[0], a[1]);
    let lhs = d.ineg(ab);
    let na = d.ineg(a[0]);
    let nb = d.ineg(a[1]);
    let rhs = d.iadd(na, nb);
    (lhs, rhs)
}
fn r_mul_neg(d: &mut IntDev<'_>, a: &[ExprId]) -> (ExprId, ExprId) {
    let nb = d.ineg(a[1]);
    let lhs = d.imul(a[0], nb);
    let ab = d.imul(a[0], a[1]);
    let rhs = d.ineg(ab);
    (lhs, rhs)
}
fn r_add_comm(d: &mut IntDev<'_>, a: &[ExprId]) -> (ExprId, ExprId) {
    (d.iadd(a[0], a[1]), d.iadd(a[1], a[0]))
}
fn r_mul_comm(d: &mut IntDev<'_>, a: &[ExprId]) -> (ExprId, ExprId) {
    (d.imul(a[0], a[1]), d.imul(a[1], a[0]))
}

/// The default ℤ rewrite set — see the module docs' table.
pub(crate) fn default_rules(p: &IntPrelude) -> Vec<Rule> {
    use Orientation::Forward;
    vec![
        Rule {
            name: p.add_zero,
            arity: 1,
            orientation: Forward,
            build: r_add_zero,
        },
        Rule {
            name: p.add_neg,
            arity: 1,
            orientation: Forward,
            build: r_add_neg,
        },
        Rule {
            name: p.add_neg_cancel_right,
            arity: 2,
            orientation: Forward,
            build: r_add_neg_cancel_right,
        },
        Rule {
            name: p.add_neg_eq_sub,
            arity: 2,
            orientation: Forward,
            build: r_add_neg_eq_sub,
        },
        Rule {
            name: p.mul_one,
            arity: 1,
            orientation: Forward,
            build: r_mul_one,
        },
        Rule {
            name: p.one_mul,
            arity: 1,
            orientation: Forward,
            build: r_one_mul,
        },
        Rule {
            name: p.neg_one_mul,
            arity: 1,
            orientation: Forward,
            build: r_neg_one_mul,
        },
        Rule {
            name: p.mul_zero,
            arity: 1,
            orientation: Forward,
            build: r_mul_zero,
        },
        Rule {
            name: p.neg_add,
            arity: 2,
            orientation: Forward,
            build: r_neg_add,
        },
        Rule {
            name: p.mul_neg,
            arity: 2,
            orientation: Forward,
            build: r_mul_neg,
        },
    ]
}

/// The default set plus caller-supplied extras — see [`super::nat::with_extra`].
pub(crate) fn with_extra(defaults: &[Rule], extra: &[Rule]) -> Vec<Rule> {
    let mut rules = defaults.to_vec();
    rules.extend_from_slice(extra);
    rules
}

/// `Int.add_comm` as a caller-supplied extra — see the module docs on why
/// this is safe only when the goal's fixed point fully annihilates.
pub(crate) fn rule_add_comm(p: &IntPrelude) -> Rule {
    Rule {
        name: p.add_comm,
        arity: 2,
        orientation: Orientation::Forward,
        build: r_add_comm,
    }
}

/// `Int.mul_comm` as a caller-supplied extra — as [`rule_add_comm`].
pub(crate) fn rule_mul_comm(p: &IntPrelude) -> Rule {
    Rule {
        name: p.mul_comm,
        arity: 2,
        orientation: Orientation::Forward,
        build: r_mul_comm,
    }
}

// --- matching (identical shape to `super::nat`, over `IntDev`) -----------

fn instantiate(d: &mut IntDev<'_>, rule: &Rule) -> (Vec<ExprId>, ExprId, ExprId) {
    let vars: Vec<ExprId> = (0..rule.arity)
        .map(|_| {
            let fv = d.fresh_fvar();
            d.kernel().fvar(fv)
        })
        .collect();
    let (lhs, rhs) = (rule.build)(d, &vars);
    (vars, lhs, rhs)
}

fn try_match(
    d: &mut IntDev<'_>,
    pattern_vars: &[ExprId],
    pattern: ExprId,
    target: ExprId,
    bindings: &mut [Option<ExprId>],
) -> bool {
    if let Some(pos) = pattern_vars.iter().position(|&v| v == pattern) {
        return if let Some(bound) = bindings[pos] {
            bound == target
        } else {
            bindings[pos] = Some(target);
            true
        };
    }
    if pattern == target {
        return true;
    }
    let pn = d.kernel().expr_node(pattern).clone();
    let tn = d.kernel().expr_node(target).clone();
    match (pn, tn) {
        (ExprNode::App(f1, a1), ExprNode::App(f2, a2)) => {
            try_match(d, pattern_vars, f1, f2, bindings)
                && try_match(d, pattern_vars, a1, a2, bindings)
        }
        _ => false,
    }
}

fn try_rewrite_at(d: &mut IntDev<'_>, rules: &[Rule], e: ExprId) -> Option<(ExprId, ExprId)> {
    for rule in rules {
        let (vars, lhs_pat, rhs_pat) = instantiate(d, rule);
        let pattern = match rule.orientation {
            Orientation::Forward => lhs_pat,
            Orientation::Backward => rhs_pat,
        };
        let mut bindings: Vec<Option<ExprId>> = vec![None; rule.arity];
        if !try_match(d, &vars, pattern, e, &mut bindings) {
            continue;
        }
        let args: Vec<ExprId> = match bindings.into_iter().collect::<Option<Vec<_>>>() {
            Some(a) => a,
            None => continue,
        };
        let (lhs_c, rhs_c) = (rule.build)(d, &args);
        let lemma_proof = d.lemma(rule.name, &args);
        let (new_e, proof) = match rule.orientation {
            Orientation::Forward => {
                debug_assert_eq!(lhs_c, e, "matched pattern must reconstruct the target");
                (rhs_c, lemma_proof)
            }
            Orientation::Backward => {
                debug_assert_eq!(rhs_c, e, "matched pattern must reconstruct the target");
                (lhs_c, d.isymm(lhs_c, rhs_c, lemma_proof))
            }
        };
        return Some((new_e, proof));
    }
    None
}

/// Outermost-first, spine-aware over `Int.add`/`Int.mul`/`Int.neg` — see
/// [`super::nat::rewrite_step`]'s docs on why this must dispatch on the
/// operator rather than doing a blind generic `App` descent (`IntDev::icongr`
/// is hardcoded to `Eq Int _ _`, exactly as `NatOps::congr` is to `Eq Nat`).
fn rewrite_step(d: &mut IntDev<'_>, rules: &[Rule], e: ExprId) -> Option<(ExprId, ExprId)> {
    if let Some(step) = try_rewrite_at(d, rules, e) {
        return Some(step);
    }
    let p = d.int();
    let (head, args) = spine(d, e);
    let name = head_const(d, head)?;
    if name == p.add && args.len() == 2 {
        return rewrite_binary(d, rules, args[0], args[1], &|d, x, y| d.iadd(x, y));
    }
    if name == p.mul && args.len() == 2 {
        return rewrite_binary(d, rules, args[0], args[1], &|d, x, y| d.imul(x, y));
    }
    if name == p.neg && args.len() == 1 {
        return rewrite_unary(d, rules, args[0], &|d, x| d.ineg(x));
    }
    None
}

fn rewrite_binary(
    d: &mut IntDev<'_>,
    rules: &[Rule],
    u: ExprId,
    v: ExprId,
    op: &dyn Fn(&mut IntDev<'_>, ExprId, ExprId) -> ExprId,
) -> Option<(ExprId, ExprId)> {
    if let Some((u2, hu)) = rewrite_step(d, rules, u) {
        let new_e = op(d, u2, v);
        let proof = d.icongr(u, u2, hu, &|d, x| op(d, x, v));
        return Some((new_e, proof));
    }
    if let Some((v2, hv)) = rewrite_step(d, rules, v) {
        let new_e = op(d, u, v2);
        let proof = d.icongr(v, v2, hv, &|d, x| op(d, u, x));
        return Some((new_e, proof));
    }
    None
}

fn rewrite_unary(
    d: &mut IntDev<'_>,
    rules: &[Rule],
    u: ExprId,
    op: &dyn Fn(&mut IntDev<'_>, ExprId) -> ExprId,
) -> Option<(ExprId, ExprId)> {
    let (u2, hu) = rewrite_step(d, rules, u)?;
    let new_e = op(d, u2);
    let proof = d.icongr(u, u2, hu, &|d, x| op(d, x));
    Some((new_e, proof))
}

fn rewrite_to_fixpoint(
    d: &mut IntDev<'_>,
    rules: &[Rule],
    start: ExprId,
) -> Result<(ExprId, ExprId, usize), Decline> {
    let mut current = start;
    let mut steps: Vec<(ExprId, ExprId)> = Vec::new();
    for _ in 0..MAX_STEPS {
        if let Some((next, proof)) = rewrite_step(d, rules, current) {
            steps.push((next, proof));
            current = next;
        } else {
            let (_last, proof) = d.ichain(start, &steps);
            return Ok((current, proof, steps.len()));
        }
    }
    if rewrite_step(d, rules, current).is_some() {
        return Err(Decline::BudgetExceeded);
    }
    let (_last, proof) = d.ichain(start, &steps);
    Ok((current, proof, steps.len()))
}

/// Rewrite `start` to a fixed point under `rules`, returning
/// `(final_term, proof: Eq start final_term)` — [`rewrite_to_fixpoint`]
/// without the step count, for a caller (`crate::tactic::int`'s
/// `Then(Simp, _)`) that wants the normal form of a single, unpaired term
/// rather than a proof of an already-stated `Eq` goal. Mirrors
/// `super::nat::normalize` exactly — see that function's docs for why
/// nothing else in this module needed to move.
///
/// # Errors
///
/// [`Decline::BudgetExceeded`], as [`rewrite_to_fixpoint`].
pub(crate) fn normalize(
    d: &mut IntDev<'_>,
    rules: &[Rule],
    start: ExprId,
) -> Result<(ExprId, ExprId), Decline> {
    let (final_term, proof, _steps) = rewrite_to_fixpoint(d, rules, start)?;
    Ok((final_term, proof))
}

fn prove_eq_inner(
    d: &mut IntDev<'_>,
    rules: &[Rule],
    lhs: ExprId,
    rhs: ExprId,
    verify: bool,
) -> Result<ExprId, Decline> {
    let (lhs_final, lhs_proof, lhs_steps) = rewrite_to_fixpoint(d, rules, lhs)?;
    let (rhs_final, rhs_proof, rhs_steps) = rewrite_to_fixpoint(d, rules, rhs)?;
    if lhs_steps == 0 && rhs_steps == 0 {
        return Err(Decline::NoProgress);
    }
    if verify && lhs_final != rhs_final {
        return Err(Decline::SidesDiffer);
    }
    let rhs_back = d.isymm(rhs, rhs_final, rhs_proof);
    Ok(d.itrans(lhs, lhs_final, rhs, lhs_proof, rhs_back))
}

/// Prove `Eq Int lhs rhs` by rewriting both sides to a fixed point under
/// `rules`, or decline. See [`super::nat::prove_eq`].
///
/// # Errors
///
/// As [`super::nat::prove_eq`].
pub(crate) fn prove_eq(
    d: &mut IntDev<'_>,
    rules: &[Rule],
    lhs: ExprId,
    rhs: ExprId,
) -> Result<ExprId, Decline> {
    prove_eq_inner(d, rules, lhs, rhs, true)
}

/// [`prove_eq`] with the procedure's own convergence check switched off —
/// see [`super::nat::prove_eq_unverified`].
///
/// # Errors
///
/// As [`prove_eq`], minus [`Decline::SidesDiffer`].
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) fn prove_eq_unverified(
    d: &mut IntDev<'_>,
    rules: &[Rule],
    lhs: ExprId,
    rhs: ExprId,
) -> Result<ExprId, Decline> {
    prove_eq_inner(d, rules, lhs, rhs, false)
}

fn spine(d: &mut IntDev<'_>, e: ExprId) -> (ExprId, Vec<ExprId>) {
    let mut args = Vec::new();
    let mut head = e;
    loop {
        let node = d.kernel().expr_node(head).clone();
        let ExprNode::App(f, a) = node else { break };
        args.push(a);
        head = f;
    }
    args.reverse();
    (head, args)
}

fn head_const(d: &mut IntDev<'_>, e: ExprId) -> Option<NameId> {
    match d.kernel().expr_node(e).clone() {
        ExprNode::Const(n, _) => Some(n),
        _ => None,
    }
}

/// Why [`theorem`] produced no declaration.
#[derive(Debug)]
pub(crate) enum SimpError {
    /// The procedure declined.
    Declined(Decline),
    /// The procedure emitted a term and the **kernel** refused it.
    Rejected(crate::KernelError),
}

impl core::fmt::Display for SimpError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::Declined(d) => write!(f, "simp declined: {d:?}"),
            Self::Rejected(e) => write!(f, "kernel rejected the emitted term: {e:?}"),
        }
    }
}

/// Declare `theorem name : ∀ x₀ … x_{arity−1}, Eq Int lhs rhs`, with `build`
/// returning `(lhs, rhs)` over `arity` fresh args and the proof searched for
/// and emitted, never written by hand.
///
/// # Errors
///
/// [`SimpError::Declined`] when the procedure found no term, or
/// [`SimpError::Rejected`] when the kernel refused the one it found.
pub(crate) fn theorem(
    d: &mut IntDev<'_>,
    rules: &[Rule],
    name: NameId,
    arity: usize,
    build: &dyn Fn(&mut IntDev<'_>, &[ExprId]) -> (ExprId, ExprId),
) -> Result<NameId, SimpError> {
    let int_ty = d.int_ty();
    let fvs: Vec<u64> = (0..arity).map(|_| d.fresh_fvar()).collect();
    let vars: Vec<ExprId> = fvs.iter().map(|&f| d.kernel().fvar(f)).collect();
    let (lhs, rhs) = build(d, &vars);

    let proof = prove_eq(d, rules, lhs, rhs).map_err(SimpError::Declined)?;

    let mut ty = d.ieq(lhs, rhs);
    let mut value = proof;
    for &fv in fvs.iter().rev() {
        ty = d.pi_fv(fv, int_ty, ty);
        value = d.lam_fv(fv, int_ty, value);
    }
    d.kernel()
        .add_declaration(crate::env::Declaration::Theorem {
            name,
            uparams: vec![],
            ty,
            value,
        })
        .map_err(SimpError::Rejected)?;
    Ok(name)
}

/// [`theorem`], with the outcome collapsed into the prelude build's own
/// error channel so a call site can use `?` alongside the hand-written
/// declarations around it — see `ring::nat::declare`'s docs for why the
/// `UnknownConst` mapping on decline is exact rather than approximate.
///
/// # Errors
///
/// The kernel's rejection when the emitted term was refused, or
/// `UnknownConst { name }` when the search declined and no term was built.
pub(crate) fn declare(
    d: &mut IntDev<'_>,
    rules: &[Rule],
    name: NameId,
    arity: usize,
    build: &dyn Fn(&mut IntDev<'_>, &[ExprId]) -> (ExprId, ExprId),
) -> Result<(), crate::KernelError> {
    match theorem(d, rules, name, arity, build) {
        Ok(_) => Ok(()),
        Err(SimpError::Rejected(e)) => Err(e),
        Err(SimpError::Declined(_)) => Err(crate::KernelError::UnknownConst { name }),
    }
}
