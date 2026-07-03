//! `nullable`, the transition-regex **derivative**, similarity
//! canonicalization, and the derivative closure (T-C.2).
//!
//! This is the core of the symbolic-derivative membership engine (ADR-0054,
//! PLDI 2021; Brzozowski 1964). Given a [`Regex`] over [`CharPred`] leaves:
//!
//! * [`nullable`] decides whether the regex accepts `ε` (structural, one pass);
//! * [`derivative`] computes the **transition regex** `∂R` — a decision over
//!   disjoint [`CharPred`] guards covering the alphabet, whose leaves are the
//!   residual [`Regex`] after consuming one character in that guard. Boolean
//!   nodes push through by De Morgan (`∂(R∩S) = ∂R ∩ ∂S`, `∂(∁R) = ∁∂R`,
//!   pointwise on the minterm refinement of the local guards), so intersection
//!   and complement are lazy — no determinization;
//! * [`canon`] is the **similarity canonicalization** (ACI + absorption +
//!   idempotence normal form) that bounds the derivative set (Brzozowski
//!   finiteness), and [`derivative_closure`] enumerates the reachable
//!   canonical residuals under a budget.
//!
//! Native bounded loops [`Regex::Loop`] are stepped natively (`∂(R{n,m})`), never
//! pre-unrolled (LPAR 2024): the loop count is decremented, saturating the lower
//! bound at 0 and treating `hi = None` as `ω`.
//!
//! References: Brzozowski 1964; Owens et al. JFP 2009; PLDI 2021; LPAR 2024;
//! ADR-0054. Correctness is anchored by the independent
//! [`matcher`](super::matcher) via the fundamental-derivative-theorem property
//! test.

use std::collections::BTreeSet;

use super::ast::Regex;
use super::predicate::CharPred;

/// Whether `r` accepts the empty string `ε`.
///
/// Structural, one pass: [`Comp`](Regex::Comp) flips,
/// [`Inter`](Regex::Inter) is `∧`, [`Union`](Regex::Union) is `∨`,
/// [`Star`](Regex::Star) is always nullable, and a [`Loop`](Regex::Loop)
/// `R{lo,hi}` is nullable iff `lo == 0` (zero copies match `ε`) or `R` itself
/// is nullable (each of `lo > 0` copies can then match `ε`).
#[must_use]
pub fn nullable(r: &Regex) -> bool {
    match r {
        Regex::Empty | Regex::Star(_) => true,
        Regex::None | Regex::Pred(_) => false,
        Regex::Concat(a, b) | Regex::Inter(a, b) => nullable(a) && nullable(b),
        Regex::Union(a, b) => nullable(a) || nullable(b),
        Regex::Comp(a) => !nullable(a),
        Regex::Loop { inner, lo, .. } => *lo == 0 || nullable(inner),
    }
}

/// A **transition regex**: a decision over disjoint [`CharPred`] guards, whose
/// leaves are the residual [`Regex`] after consuming one character in that
/// guard (ADR-0054 / PLDI 2021).
///
/// The guards are pairwise disjoint and their union is the entire alphabet, so
/// exactly one branch matches any code point ([`step`](Self::step)). Leaves are
/// already [`canon`]-normalized, and branches with the same residual are
/// coalesced so the transition regex stays small.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TransitionRegex {
    branches: Vec<(CharPred, Regex)>,
}

impl TransitionRegex {
    /// The `(guard, residual)` branches (disjoint guards covering the alphabet).
    #[must_use]
    pub fn branches(&self) -> &[(CharPred, Regex)] {
        &self.branches
    }

    /// The residual regex for the unique branch whose guard contains `c`.
    ///
    /// Returns [`Regex::None`] only if `c` is outside the alphabet (no guard
    /// matches); within the alphabet the guards cover every code point.
    #[must_use]
    pub fn step(&self, c: u32) -> &Regex {
        for (guard, residual) in &self.branches {
            if guard.contains(c) {
                return residual;
            }
        }
        &Regex::None
    }
}

/// Coalesce raw `(guard, residual)` pairs into a canonical transition regex:
/// drop empty guards, group by residual (OR-ing their guards), sort by residual
/// for determinism.
fn coalesce(raw: Vec<(CharPred, Regex)>) -> TransitionRegex {
    // Group guards by residual. `residual` is already canon-normalized by the
    // callers below.
    let mut grouped: Vec<(Regex, CharPred)> = Vec::new();
    for (guard, residual) in raw {
        if guard.is_empty() {
            continue;
        }
        if let Some(slot) = grouped.iter_mut().find(|(r, _)| *r == residual) {
            slot.1 = slot.1.or(&guard);
        } else {
            grouped.push((residual, guard));
        }
    }
    grouped.sort_by(|a, b| a.0.cmp(&b.0));
    TransitionRegex {
        branches: grouped.into_iter().map(|(r, g)| (g, r)).collect(),
    }
}

/// Combine two transition regexes pointwise on the refinement of their guards:
/// for every pair of branches, intersect the guards (dropping empty ones) and
/// combine the residuals with `f`. Inputs cover the alphabet with disjoint
/// guards ⇒ so does the output.
fn product(
    a: &[(CharPred, Regex)],
    b: &[(CharPred, Regex)],
    f: impl Fn(&Regex, &Regex) -> Regex,
) -> Vec<(CharPred, Regex)> {
    let mut out = Vec::new();
    for (g1, r1) in a {
        for (g2, r2) in b {
            let guard = g1.and(g2);
            if !guard.is_empty() {
                out.push((guard, canon(&f(r1, r2))));
            }
        }
    }
    out
}

/// The transition-regex derivative `∂R`: after consuming one character in each
/// branch's guard, the residual leaf is the regex matching the rest.
///
/// See the [module docs](self) for the algorithm (De Morgan push-through for
/// Boolean nodes; native loop stepping). The returned guards are disjoint and
/// cover the alphabet.
#[must_use]
pub fn derivative(r: &Regex) -> TransitionRegex {
    coalesce(deriv_raw(r))
}

/// Uncoalesced derivative branches (guards disjoint, covering the alphabet).
fn deriv_raw(r: &Regex) -> Vec<(CharPred, Regex)> {
    match r {
        // ∂ε = ∂∅ = ∅ everywhere.
        Regex::Empty | Regex::None => vec![(CharPred::all(), Regex::None)],
        // ∂(pred): match ⇒ ε, else ⇒ ∅.
        Regex::Pred(p) => {
            let mut out = vec![(p.clone(), Regex::Empty)];
            let neg = p.not();
            if !neg.is_empty() {
                out.push((neg, Regex::None));
            }
            out
        }
        // ∂(R | S) = ∂R | ∂S.
        Regex::Union(a, b) => product(&deriv_raw(a), &deriv_raw(b), |x, y| {
            Regex::union(x.clone(), y.clone())
        }),
        // ∂(R & S) = ∂R & ∂S.
        Regex::Inter(a, b) => product(&deriv_raw(a), &deriv_raw(b), |x, y| {
            Regex::inter(x.clone(), y.clone())
        }),
        // ∂(∁R) = ∁∂R (pointwise).
        Regex::Comp(a) => deriv_raw(a)
            .into_iter()
            .map(|(g, d)| (g, canon(&Regex::comp(d))))
            .collect(),
        // ∂(R · S) = ∂R · S  ∪  (nullable R) ∂S.
        Regex::Concat(a, b) => {
            let part1: Vec<(CharPred, Regex)> = deriv_raw(a)
                .into_iter()
                .map(|(g, d)| (g, canon(&Regex::concat(d, (**b).clone()))))
                .collect();
            if nullable(a) {
                product(&part1, &deriv_raw(b), |x, y| {
                    Regex::union(x.clone(), y.clone())
                })
            } else {
                part1
            }
        }
        // ∂(R*) = ∂R · R*.
        Regex::Star(a) => deriv_raw(a)
            .into_iter()
            .map(|(g, d)| (g, canon(&Regex::concat(d, Regex::star((**a).clone())))))
            .collect(),
        // ∂(R{lo,hi}) — native loop step, never pre-unrolled.
        Regex::Loop { inner, lo, hi } => deriv_loop(inner, *lo, *hi),
    }
}

/// `∂(R{lo,hi})` = `∂(R · R{lo-1,hi-1})` with the lower bound saturating at 0
/// and `hi = None` treated as `ω`. Degenerate loops are folded by [`canon`],
/// which bounds the recursion (each level strictly shrinks `hi`, or shrinks
/// `lo` toward 0 with `hi = None`).
fn deriv_loop(inner: &Regex, lo: u32, hi: Option<u32>) -> Vec<(CharPred, Regex)> {
    // R{lo,0} = ε (lo must be 0), so ∂ = ∅ everywhere.
    if hi == Some(0) {
        return vec![(CharPred::all(), Regex::None)];
    }
    let lo2 = lo.saturating_sub(1);
    let hi2 = hi.map(|h| h - 1);
    let rest = canon(&Regex::repeat(inner.clone(), lo2, hi2));

    // ∂(R · rest) with `R = inner`.
    let part1: Vec<(CharPred, Regex)> = deriv_raw(inner)
        .into_iter()
        .map(|(g, d)| (g, canon(&Regex::concat(d, rest.clone()))))
        .collect();
    if nullable(inner) {
        product(&part1, &deriv_raw(&rest), |x, y| {
            Regex::union(x.clone(), y.clone())
        })
    } else {
        part1
    }
}

/// **Similarity canonicalization** (ACI + absorption + idempotence): rewrite a
/// regex to a representative that is stable under associativity, commutativity,
/// and idempotence of `|`/`&`, `∅`/`ε`/`Σ*` absorption, `∁∁R = R`,
/// `(R*)* = R*`, and loop normalizations. This is what makes the derivative
/// closure of typical regexes finite and small (Brzozowski 1964).
///
/// Every rewrite is a semantic identity, so `L(canon(R)) = L(R)`.
#[must_use]
pub fn canon(r: &Regex) -> Regex {
    match r {
        Regex::Empty | Regex::None => r.clone(),
        Regex::Pred(p) => {
            if p.is_empty() {
                Regex::None
            } else {
                r.clone()
            }
        }
        Regex::Comp(a) => {
            let a = canon(a);
            match a {
                Regex::Comp(inner) => *inner,
                other => Regex::comp(other),
            }
        }
        Regex::Star(a) => {
            let a = canon(a);
            match a {
                // (R*)* = R*, and it is already canonical.
                Regex::Star(_) => a,
                // ε* = ε, ∅* = ε.
                Regex::Empty | Regex::None => Regex::Empty,
                other => Regex::star(other),
            }
        }
        Regex::Concat(x, y) => {
            let mut items = Vec::new();
            push_concat(canon(x), &mut items);
            push_concat(canon(y), &mut items);
            if items.contains(&Regex::None) {
                return Regex::None;
            }
            items.retain(|i| *i != Regex::Empty);
            match items.len() {
                0 => Regex::Empty,
                1 => items.pop().unwrap_or(Regex::Empty),
                _ => fold_right(items, Regex::concat),
            }
        }
        Regex::Union(x, y) => {
            let mut items = Vec::new();
            push_union(canon(x), &mut items);
            push_union(canon(y), &mut items);
            items.retain(|i| *i != Regex::None);
            if items.iter().any(Regex::is_universal) {
                return Regex::universal();
            }
            items.sort();
            items.dedup();
            match items.len() {
                0 => Regex::None,
                1 => items.pop().unwrap_or(Regex::None),
                _ => fold_right(items, Regex::union),
            }
        }
        Regex::Inter(x, y) => {
            let mut items = Vec::new();
            push_inter(canon(x), &mut items);
            push_inter(canon(y), &mut items);
            if items.contains(&Regex::None) {
                return Regex::None;
            }
            items.retain(|i| !i.is_universal());
            items.sort();
            items.dedup();
            match items.len() {
                0 => Regex::universal(),
                1 => items.pop().unwrap_or_else(Regex::universal),
                _ => fold_right(items, Regex::inter),
            }
        }
        Regex::Loop { inner, lo, hi } => canon_loop(canon(inner), *lo, *hi),
    }
}

/// Normalize a loop over an already-canonical `inner`.
fn canon_loop(inner: Regex, lo: u32, hi: Option<u32>) -> Regex {
    // Empty range ⇒ ∅.
    if let Some(h) = hi
        && lo > h
    {
        return Regex::None;
    }
    match &inner {
        // ∅{0,_} = ε (the zero-copy string); ∅{lo>0,_} = ∅.
        Regex::None => return if lo == 0 { Regex::Empty } else { Regex::None },
        // ε repeated any count is ε.
        Regex::Empty => return Regex::Empty,
        _ => {}
    }
    if lo == 0 && hi == Some(0) {
        return Regex::Empty;
    }
    if lo == 1 && hi == Some(1) {
        return inner;
    }
    if lo == 0 && hi.is_none() {
        return Regex::star(inner);
    }
    Regex::repeat(inner, lo, hi)
}

/// Flatten a right-associated concat spine, pushing leaves in order.
fn push_concat(r: Regex, out: &mut Vec<Regex>) {
    match r {
        Regex::Concat(a, b) => {
            push_concat(*a, out);
            push_concat(*b, out);
        }
        other => out.push(other),
    }
}

/// Flatten a union tree into its leaf set (order-independent; sorted later).
fn push_union(r: Regex, out: &mut Vec<Regex>) {
    match r {
        Regex::Union(a, b) => {
            push_union(*a, out);
            push_union(*b, out);
        }
        other => out.push(other),
    }
}

/// Flatten an intersection tree into its leaf set.
fn push_inter(r: Regex, out: &mut Vec<Regex>) {
    match r {
        Regex::Inter(a, b) => {
            push_inter(*a, out);
            push_inter(*b, out);
        }
        other => out.push(other),
    }
}

/// Rebuild a right-associated binary tree from `items` (`len >= 2`) using `f`.
fn fold_right(items: Vec<Regex>, f: impl Fn(Regex, Regex) -> Regex) -> Regex {
    let mut iter = items.into_iter().rev();
    let mut acc = iter.next().expect("fold_right: non-empty");
    for item in iter {
        acc = f(item, acc);
    }
    acc
}

/// The reachable set of canonical residual regexes under repeated derivatives,
/// or a budget overrun.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Closure {
    /// The full reachable set (including the start regex), each element
    /// [`canon`]-normalized. Its size is the derivative-state count.
    Complete(Vec<Regex>),
    /// The reachable set exceeded `max_states` residuals before closing.
    Budget,
}

/// Enumerate the canonical derivative closure of `regex`: the set of residuals
/// reachable by any sequence of derivative steps (Brzozowski's finite set up to
/// similarity). Returns [`Closure::Budget`] if more than `max_states` distinct
/// canonical residuals are reached — the first-class `unknown` guard.
///
/// This is the finiteness witness used by the closure-finiteness tests and,
/// later, by derivative-emptiness reasoning.
#[must_use]
pub fn derivative_closure(regex: &Regex, max_states: usize) -> Closure {
    let start = canon(regex);
    let mut seen: BTreeSet<Regex> = BTreeSet::new();
    let mut worklist: Vec<Regex> = vec![start.clone()];
    seen.insert(start);
    while let Some(state) = worklist.pop() {
        for (_, residual) in derivative(&state).branches {
            if !seen.contains(&residual) {
                if seen.len() >= max_states {
                    return Closure::Budget;
                }
                seen.insert(residual.clone());
                worklist.push(residual);
            }
        }
    }
    Closure::Complete(seen.into_iter().collect())
}
