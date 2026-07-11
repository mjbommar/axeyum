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

/// Combine two transition regexes pointwise on the refinement of their guards
/// with a caller **stop poll** (`over`) checked once per guard pair. This is
/// the multiplicative frontier of the derivative: `|a| · |b|` pairs, each a
/// guard intersection plus a residual [`canon`]. On a Σ*-enlarged intersection
/// this loop is where a single derivative spends a long, otherwise
/// deadline-uninterruptible interval, so `over` lets the caller abandon it
/// mid-product (⇒ `None`, which the closure/witness search turns into a timely
/// decline). Returns `Some(branches)` when the loop completes within budget.
fn product_within<F: FnMut() -> bool>(
    a: &[(CharPred, Regex)],
    b: &[(CharPred, Regex)],
    f: impl Fn(&Regex, &Regex) -> Regex,
    over: &mut F,
) -> Option<Vec<(CharPred, Regex)>> {
    let mut out = Vec::new();
    for (g1, r1) in a {
        for (g2, r2) in b {
            if over() {
                return None;
            }
            let guard = g1.and(g2);
            if !guard.is_empty() {
                let residual = canon_within(&f(r1, r2), over)?;
                out.push((guard, residual));
            }
        }
    }
    Some(out)
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

/// [`derivative`] with a caller **stop poll** threaded **into** the computation:
/// `over` is checked at every recursion node and every `product_within` guard pair,
/// so a single derivative over a deeply-nested, `Σ*`-enlarged intersection is
/// **interruptible mid-flight** and returns [`None`] once `over` trips — the
/// same first-class decline an exhausted budget produces elsewhere.
///
/// This closes the deadline hole the plain [`derivative`] leaves: the between-node
/// deadline polls in the closure and witness searches only fire *between* whole
/// derivatives, so one pathological derivative (its `product` cascade multiplies
/// branch counts before `coalesce` prunes them) could run well past a wall-clock
/// deadline before the next node-level poll. Threading the poll into the frontier
/// bounds that overshoot to a single poll interval. Result-identical to
/// [`derivative`] whenever `over` never trips.
#[must_use]
pub fn derivative_within<F: FnMut() -> bool>(r: &Regex, over: &mut F) -> Option<TransitionRegex> {
    Some(coalesce(deriv_raw_within(r, over)?))
}

/// Uncoalesced derivative branches (guards disjoint, covering the alphabet).
fn deriv_raw(r: &Regex) -> Vec<(CharPred, Regex)> {
    deriv_raw_within(r, &mut || false)
        .expect("deriv_raw_within with a never-tripping budget cannot abort")
}

/// [`deriv_raw`] with a caller **stop poll** (`over`) checked at every recursion
/// node and threaded through every [`product_within`]. Returns [`None`] as soon
/// as `over` trips, so an expensive derivative is a timely decline rather than a
/// deadline-uninterruptible grind. With a never-tripping `over` it is exactly
/// [`deriv_raw`] (the identity the fundamental-derivative-theorem property test
/// anchors, since [`derivative`] routes through this function).
fn deriv_raw_within<F: FnMut() -> bool>(r: &Regex, over: &mut F) -> Option<Vec<(CharPred, Regex)>> {
    if over() {
        return None;
    }
    Some(match r {
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
        Regex::Union(a, b) => {
            let da = deriv_raw_within(a, over)?;
            let db = deriv_raw_within(b, over)?;
            return product_within(&da, &db, |x, y| Regex::union(x.clone(), y.clone()), over);
        }
        // ∂(R & S) = ∂R & ∂S.
        Regex::Inter(a, b) => {
            let da = deriv_raw_within(a, over)?;
            let db = deriv_raw_within(b, over)?;
            return product_within(&da, &db, |x, y| Regex::inter(x.clone(), y.clone()), over);
        }
        // ∂(∁R) = ∁∂R (pointwise).
        Regex::Comp(a) => {
            let mut out = Vec::new();
            for (g, d) in deriv_raw_within(a, over)? {
                out.push((g, canon_within(&Regex::comp(d), over)?));
            }
            out
        }
        // ∂(R · S) = ∂R · S  ∪  (nullable R) ∂S.
        Regex::Concat(a, b) => {
            let mut part1: Vec<(CharPred, Regex)> = Vec::new();
            for (g, d) in deriv_raw_within(a, over)? {
                part1.push((g, canon_within(&Regex::concat(d, (**b).clone()), over)?));
            }
            if nullable(a) {
                let db = deriv_raw_within(b, over)?;
                return product_within(
                    &part1,
                    &db,
                    |x, y| Regex::union(x.clone(), y.clone()),
                    over,
                );
            }
            part1
        }
        // ∂(R*) = ∂R · R*.
        Regex::Star(a) => {
            let mut out = Vec::new();
            for (g, d) in deriv_raw_within(a, over)? {
                out.push((
                    g,
                    canon_within(&Regex::concat(d, Regex::star((**a).clone())), over)?,
                ));
            }
            out
        }
        // ∂(R{lo,hi}) — native loop step, never pre-unrolled.
        Regex::Loop { inner, lo, hi } => return deriv_loop_within(inner, *lo, *hi, over),
    })
}

/// `∂(R{lo,hi})` = `∂(R · R{lo-1,hi-1})` with the lower bound saturating at 0
/// and `hi = None` treated as `ω`, with a caller **stop poll** (`over`) threaded
/// through the inner [`deriv_raw_within`]/[`product_within`] so a loop step over
/// an enlarged body is interruptible too. Degenerate loops are folded by
/// [`canon`], which bounds the recursion (each level strictly shrinks `hi`, or
/// shrinks `lo` toward 0 with `hi = None`). Returns [`None`] once `over` trips.
fn deriv_loop_within<F: FnMut() -> bool>(
    inner: &Regex,
    lo: u32,
    hi: Option<u32>,
    over: &mut F,
) -> Option<Vec<(CharPred, Regex)>> {
    // R{lo,0} = ε (lo must be 0), so ∂ = ∅ everywhere.
    if hi == Some(0) {
        return Some(vec![(CharPred::all(), Regex::None)]);
    }
    let lo2 = lo.saturating_sub(1);
    let hi2 = hi.map(|h| h - 1);
    let rest = canon_within(&Regex::repeat(inner.clone(), lo2, hi2), over)?;

    // ∂(R · rest) with `R = inner`.
    let mut part1: Vec<(CharPred, Regex)> = Vec::new();
    for (g, d) in deriv_raw_within(inner, over)? {
        part1.push((g, canon_within(&Regex::concat(d, rest.clone()), over)?));
    }
    if nullable(inner) {
        let drest = deriv_raw_within(&rest, over)?;
        product_within(
            &part1,
            &drest,
            |x, y| Regex::union(x.clone(), y.clone()),
            over,
        )
    } else {
        Some(part1)
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
    canon_within(r, &mut || false).expect("canon_within with a never-tripping budget cannot abort")
}

/// [`canon`] with a caller **stop poll** (`over`) checked at every recursive
/// canonicalization node and while flattening/rebuilding associative spines.
///
/// Returns [`None`] as soon as `over` trips, letting deadline-bounded derivative
/// and membership searches decline promptly instead of spending an uninterruptible
/// interval inside one large similarity-canonicalization step. With a
/// never-tripping `over`, this is result-identical to [`canon`].
#[must_use]
pub fn canon_within<F: FnMut() -> bool>(r: &Regex, over: &mut F) -> Option<Regex> {
    if over() {
        return None;
    }
    match r {
        Regex::Empty | Regex::None => Some(r.clone()),
        Regex::Pred(p) => {
            if p.is_empty() {
                Some(Regex::None)
            } else {
                Some(r.clone())
            }
        }
        Regex::Comp(a) => {
            let a = canon_within(a, over)?;
            match a {
                Regex::Comp(inner) => Some(*inner),
                other => Some(Regex::comp(other)),
            }
        }
        Regex::Star(a) => {
            let a = canon_within(a, over)?;
            match a {
                // (R*)* = R*, and it is already canonical.
                Regex::Star(_) => Some(a),
                // ε* = ε, ∅* = ε.
                Regex::Empty | Regex::None => Some(Regex::Empty),
                other => Some(Regex::star(other)),
            }
        }
        Regex::Concat(x, y) => {
            let mut items = Vec::new();
            push_concat_within(canon_within(x, over)?, &mut items, over)?;
            push_concat_within(canon_within(y, over)?, &mut items, over)?;
            if items.contains(&Regex::None) {
                return Some(Regex::None);
            }
            items.retain(|i| *i != Regex::Empty);
            Some(match items.len() {
                0 => Regex::Empty,
                1 => items.pop().unwrap_or(Regex::Empty),
                _ => fold_right_within(items, Regex::concat, over)?,
            })
        }
        Regex::Union(x, y) => {
            let mut items = Vec::new();
            push_union_within(canon_within(x, over)?, &mut items, over)?;
            push_union_within(canon_within(y, over)?, &mut items, over)?;
            items.retain(|i| *i != Regex::None);
            if items.iter().any(Regex::is_universal) {
                return Some(Regex::universal());
            }
            items.sort();
            items.dedup();
            Some(match items.len() {
                0 => Regex::None,
                1 => items.pop().unwrap_or(Regex::None),
                _ => fold_right_within(items, Regex::union, over)?,
            })
        }
        Regex::Inter(x, y) => {
            let mut items = Vec::new();
            push_inter_within(canon_within(x, over)?, &mut items, over)?;
            push_inter_within(canon_within(y, over)?, &mut items, over)?;
            if items.contains(&Regex::None) {
                return Some(Regex::None);
            }
            items.retain(|i| !i.is_universal());
            items.sort();
            items.dedup();
            Some(match items.len() {
                0 => Regex::universal(),
                1 => items.pop().unwrap_or_else(Regex::universal),
                _ => fold_right_within(items, Regex::inter, over)?,
            })
        }
        Regex::Loop { inner, lo, hi } => Some(canon_loop(canon_within(inner, over)?, *lo, *hi)),
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
fn push_concat_within<F: FnMut() -> bool>(
    r: Regex,
    out: &mut Vec<Regex>,
    over: &mut F,
) -> Option<()> {
    if over() {
        return None;
    }
    match r {
        Regex::Concat(a, b) => {
            push_concat_within(*a, out, over)?;
            push_concat_within(*b, out, over)?;
        }
        other => out.push(other),
    }
    Some(())
}

/// Flatten a union tree into its leaf set (order-independent; sorted later).
fn push_union_within<F: FnMut() -> bool>(
    r: Regex,
    out: &mut Vec<Regex>,
    over: &mut F,
) -> Option<()> {
    if over() {
        return None;
    }
    match r {
        Regex::Union(a, b) => {
            push_union_within(*a, out, over)?;
            push_union_within(*b, out, over)?;
        }
        other => out.push(other),
    }
    Some(())
}

/// Flatten an intersection tree into its leaf set.
fn push_inter_within<F: FnMut() -> bool>(
    r: Regex,
    out: &mut Vec<Regex>,
    over: &mut F,
) -> Option<()> {
    if over() {
        return None;
    }
    match r {
        Regex::Inter(a, b) => {
            push_inter_within(*a, out, over)?;
            push_inter_within(*b, out, over)?;
        }
        other => out.push(other),
    }
    Some(())
}

/// Rebuild a right-associated binary tree from `items` (`len >= 2`) using `f`.
fn fold_right_within<F: FnMut() -> bool>(
    items: Vec<Regex>,
    f: impl Fn(Regex, Regex) -> Regex,
    over: &mut F,
) -> Option<Regex> {
    let mut iter = items.into_iter().rev();
    let mut acc = iter.next().expect("fold_right: non-empty");
    for item in iter {
        if over() {
            return None;
        }
        acc = f(item, acc);
    }
    Some(acc)
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
    derivative_closure_within(regex, max_states, || false)
}

/// [`derivative_closure`] with a caller **stop poll**: `over_deadline` is checked
/// every few expansions and, when it returns `true`, the enumeration abandons with
/// [`Closure::Budget`] — exactly as an exhausted `max_states` budget does.
///
/// Materializing the closure of a complex regex (a `re.comp`/`re.inter` intersected
/// with `Σ*` runs) can visit thousands of residuals, each requiring a `derivative` +
/// `canon` that is itself non-trivial, so the plain [`derivative_closure`] can run
/// well past a wall-clock deadline before the `max_states` guard trips. This variant
/// lets a deadline-bounded caller (the online string route's per-assert emptiness
/// refuter and its `sat`-branch witnessing) keep the closure a first-class, timely
/// `unknown`. The poll is honored **both** between nodes and inside the initial
/// canonicalization ([`canon_within`]) plus each derivative ([`derivative_within`]),
/// so even one pathological, `Σ*`-enlarged derivative cannot run uninterrupted
/// for a whole between-node window. A `Closure::Budget` is always sound: emptiness
/// reasoning only ever concludes `unsat` on a **`Complete`** nullable-free closure,
/// so an abandoned closure simply declines.
#[must_use]
pub fn derivative_closure_within(
    regex: &Regex,
    max_states: usize,
    mut over_deadline: impl FnMut() -> bool,
) -> Closure {
    let Some(start) = canon_within(regex, &mut over_deadline) else {
        return Closure::Budget;
    };
    let mut seen: BTreeSet<Regex> = BTreeSet::new();
    let mut worklist: Vec<Regex> = vec![start.clone()];
    seen.insert(start);
    let mut steps: u32 = 0;
    while let Some(state) = worklist.pop() {
        // `Instant::now()` is not free; poll *between* nodes only every 64
        // expansions (cheap when most derivatives are tiny).
        steps = steps.wrapping_add(1);
        if steps.is_multiple_of(64) && over_deadline() {
            return Closure::Budget;
        }
        // Poll the deadline INSIDE the derivative/canonicalization frontier too.
        // The 64-expansion window above is uninterruptible, so a single derivative
        // over a `Σ*`-enlarged intersection (whose `product` multiplies branch
        // counts before `coalesce` prunes them) could grind for the whole window
        // — up to ~64 × the per-derivative cost — before the next between-node
        // poll. The
        // frontier poll (checked every 256 guard pairs, `Instant` amortized) bounds
        // that overshoot to a single poll interval; a tripped poll ⇒ `None` ⇒ the
        // same timely `Budget` decline the other bounds produce.
        let mut ticks: u32 = 0;
        let mut poll = || {
            ticks = ticks.wrapping_add(1);
            ticks.is_multiple_of(256) && over_deadline()
        };
        let Some(tr) = derivative_within(&state, &mut poll) else {
            return Closure::Budget;
        };
        for (_, residual) in tr.branches {
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
