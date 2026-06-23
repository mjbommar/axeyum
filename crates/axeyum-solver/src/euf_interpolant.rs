//! Ground Craig interpolation for the theory of equality with uninterpreted
//! functions (`QF_UF`), read off the congruence-closure explanation (Track 3,
//! **T3.8.3**).
//!
//! Given an unsatisfiable conjunction `A ∧ B` of equality / disequality literals
//! over uninterpreted terms, a Craig interpolant `I` satisfies `A ⇒ I`,
//! `I ∧ B ⇒ ⊥`, and uses only **shared** terms (those occurring in both `A` and
//! `B`). For EUF the refutation is a disequality `s ≠ t` whose two sides the
//! congruence closure (built from the asserted equalities) proves equal. The
//! interpolant is a *summary* of that equality proof restricted to the side that
//! does not own the disequality (`McMillan`; Fuchs et al., *Ground interpolation
//! for the theory of equality*).
//!
//! ## Method
//!
//! 1. Build a congruence-closure e-graph over all atoms, tagging each asserted
//!    equality with its partition (`A` or `B`).
//! 2. Find the violated disequality `s ≠ t` (some `diseq` whose sides are
//!    congruent) and ask the e-graph to **explain** `s = t` as a structured
//!    proof path of `Input` (asserted) and `Congruence` (derived) steps.
//! 3. Thread the steps into a single oriented `s → t` chain and **color** each by
//!    its partition: an `Input` edge by which side asserted it; a `Congruence`
//!    edge by the common color of all its argument sub-proofs (declining if an
//!    edge is *mixed*-color — sound but incomplete).
//! 4. Merge consecutive same-color edges into maximal segments. Summarize each
//!    maximal segment that belongs to the partition opposite the disequality into
//!    an equality `x = y` over its (shared) endpoint terms.
//! 5. Combine: `I = ⋀ summarized-equalities` when `s ≠ t ∈ B`, or
//!    `I = ¬ ⋀ summarized-equalities` when `s ≠ t ∈ A`.
//!
//! Every produced interpolant is **independently re-verified** — vocabulary,
//! `A ∧ ¬I` unsat, and `I ∧ B` unsat via [`check_qf_uf`] — and any failure
//! declines to `Ok(None)` rather than returning an unverified interpolant. The
//! generator is deliberately partial (equality/disequality conjunctions, a single
//! disequality conflict, monochrome congruence edges, shared segment boundaries);
//! anything outside that scope declines cleanly.

use std::collections::{BTreeSet, HashMap};

use axeyum_cnf::AletheCommand;
use axeyum_egraph::{EGraph, ENodeId, ProofStep};
use axeyum_ir::{Op, TermArena, TermId, TermNode};

use crate::{CheckResult, SolverError, check_qf_uf, prove_qf_uf_unsat_alethe};

/// Which side of the partition an atom or proof edge belongs to.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Side {
    A,
    B,
}

/// Produces a verified ground EUF Craig interpolant for the unsatisfiable
/// conjunction `A ∧ B` (`a_assertions` is `A`, `b_assertions` is `B`), each a
/// conjunction of equality / disequality literals over uninterpreted terms.
///
/// Returns `Ok(Some(I))` with a fully re-checked interpolant, or `Ok(None)` when
/// no ground interpolant is produced in the supported fragment (non-conjunctive
/// structure, a non-disequality conflict, a mixed-color or non-shared-boundary
/// proof, or a candidate that fails its independent re-checks). Never returns an
/// unverified interpolant.
///
/// # Errors
///
/// Currently infallible at the `Result` layer (all decline paths return
/// `Ok(None)`); the signature mirrors [`crate::lra_interpolant`] so the two
/// theories share a dispatch shape.
pub fn qf_uf_interpolant(
    arena: &mut TermArena,
    a_assertions: &[TermId],
    b_assertions: &[TermId],
) -> Result<Option<TermId>, SolverError> {
    build_verified_qf_uf_interpolant(arena, a_assertions, b_assertions)
}

/// Builds the congruence-summary EUF interpolant `I` for the unsatisfiable
/// conjunction `A ∧ B`, re-verifies the three Craig conditions independently, and
/// returns it (or `None`). This is the single source of truth for the interpolant
/// `I`; [`qf_uf_interpolant`] forwards to it directly and
/// [`qf_uf_interpolant_certified`] reuses it, so the returned `I` is byte-identical
/// across both entry points.
///
/// The `Result` is currently infallible (every decline path returns `Ok(None)`)
/// but is kept to mirror [`qf_uf_interpolant`]'s public signature and the LRA
/// [`crate::lra_interpolant`] dispatch shape, and to leave room for a future
/// `SolverError` decision path.
#[allow(clippy::unnecessary_wraps)]
fn build_verified_qf_uf_interpolant(
    arena: &mut TermArena,
    a_assertions: &[TermId],
    b_assertions: &[TermId],
) -> Result<Option<TermId>, SolverError> {
    // 1. Collect equality / disequality literals per side.
    let mut eqs: Vec<(TermId, TermId, Side)> = Vec::new();
    let mut diseqs: Vec<(TermId, TermId, Side)> = Vec::new();
    for (side, asserts) in [(Side::A, a_assertions), (Side::B, b_assertions)] {
        for &assertion in asserts {
            if collect_literals(arena, assertion, false, side, &mut eqs, &mut diseqs).is_none() {
                return Ok(None); // structure outside conjunctive eq/diseq → decline.
            }
        }
    }

    // 2. Build the e-graph: intern every atom term, then assert the equalities.
    let mut bridge = Bridge::new();
    for &(x, y, _) in eqs.iter().chain(&diseqs) {
        if bridge.add_term(arena, x).is_none() || bridge.add_term(arena, y).is_none() {
            return Ok(None);
        }
    }
    for (reason, &(x, y, side)) in eqs.iter().enumerate() {
        let (Some(nx), Some(ny)) = (bridge.node_of(x), bridge.node_of(y)) else {
            return Ok(None);
        };
        let Ok(reason) = u32::try_from(reason) else {
            return Ok(None); // absurdly many equalities; decline gracefully.
        };
        bridge.egraph.merge(nx, ny, reason);
        bridge.reason_side.push(side);
    }

    // 3. Find the first violated disequality (sides congruent).
    let mut conflict: Option<(ENodeId, ENodeId, Side)> = None;
    for &(x, y, side) in &diseqs {
        let (Some(nx), Some(ny)) = (bridge.node_of(x), bridge.node_of(y)) else {
            continue;
        };
        if bridge.egraph.equal(nx, ny) {
            conflict = Some((nx, ny, side));
            break;
        }
    }
    let Some((ns, nt, pd)) = conflict else {
        return Ok(None); // no disequality conflict (sat, or a non-EUF-eq refutation).
    };

    // 4. Summarize the proof `s = t`, collecting the equalities the partition
    //    OPPOSITE the disequality contributes, expressed over shared terms. The
    //    interpolant negates that conjunction when the disequality is in A.
    let summarized = match pd {
        Side::B => Side::A,
        Side::A => Side::B,
    };
    let shared = SharedTerms {
        a: subterms_of(arena, a_assertions),
        b: subterms_of(arena, b_assertions),
    };
    let mut atoms: Vec<TermId> = Vec::new();
    if summarize(&bridge, arena, ns, nt, summarized, &shared, &mut atoms).is_none() {
        return Ok(None);
    }

    // 5. Combine. `⋀ ∅ = ⊤`; the disequality side decides whether to negate.
    let conjunction = conjoin(arena, &atoms);
    let interpolant = match pd {
        Side::B => conjunction,
        Side::A => {
            let Ok(neg) = arena.not(conjunction) else {
                return Ok(None);
            };
            neg
        }
    };

    // 6. Re-verify. An empty summary is the degenerate `⊤`/`⊥` interpolant: the
    //    whole equality proof lives on the disequality's own side, so that side is
    //    unsatisfiable alone. `⊤` is a valid interpolant iff B alone is unsat
    //    (`A ⇒ ⊤`; `⊤ ∧ B = B` unsat; empty vocabulary), and dually `⊥` iff A
    //    alone is unsat. `check_qf_uf` cannot decide a bare Bool-const assertion
    //    (no equality atoms), so verify the relevant side directly.
    if atoms.is_empty() {
        let side_alone = match pd {
            Side::B => b_assertions,
            Side::A => a_assertions,
        };
        if matches!(check_qf_uf(arena, side_alone), CheckResult::Unsat) {
            return Ok(Some(interpolant));
        }
        return Ok(None);
    }

    // The general case: re-check the three Craig conditions independently.
    if verify_interpolant(arena, a_assertions, b_assertions, interpolant) {
        Ok(Some(interpolant))
    } else {
        Ok(None)
    }
}

/// A **certified** conjunctive `QF_UF` (EUF) Craig interpolant: the interpolant
/// `I` for an unsatisfiable `A ∧ B`, paired with two externally-checkable
/// congruence refutations witnessing its two soundness conditions.
///
/// - [`a_refutation`](Self::a_refutation) is an Alethe `eq_congruent` /
///   `eq_transitive` / `resolution` proof of `A ∧ ¬I ⊢ ⊥` (Craig condition 1,
///   `A ⇒ I`);
/// - [`b_refutation`](Self::b_refutation) is an Alethe congruence proof of
///   `I ∧ B ⊢ ⊥` (Craig condition 2).
///
/// Both proofs are self-validated through [`axeyum_cnf::check_alethe`] before this
/// struct is constructed (the emitter [`crate::prove_qf_uf_unsat_alethe`] returns
/// `None` on any doubt), and each is **independently** checkable by an external
/// checker — Carcara (`eq_congruent` / `eq_transitive` / `resolution`, accepted
/// when `valid && !holey`) or, via [`crate::prove_unsat_to_lean_module`] on the
/// same conjunction, the Lean kernel (`infer` + `def_eq False`, no `sorryAx`).
///
/// # Boundary
///
/// Only the CONJUNCTIVE EUF slice is certified: the interpolant `I` is a
/// conjunction of equalities over shared terms (the disequality-in-`B` case), so
/// `A ∧ ¬I` is `{A equalities} ∪ {one disequality ¬I}` and `I ∧ B` is
/// `{I equalities} ∪ {B disequality}` — each a single-disequality congruence
/// conflict [`crate::prove_qf_uf_unsat_alethe`] handles. When `I` is itself a
/// negated equality (the disequality-in-`A` case), `¬I` is **peeled** back to the
/// bare equality so the conjunction stays single-disequality. Anything the EUF
/// congruence emitter cannot refute (a multi-disequality or non-congruence
/// conjunction) declines to `Ok(None)` and stays `Validated`.
#[derive(Debug, Clone)]
pub struct QfUfInterpolantCertificate {
    /// The verified interpolant term `I` (byte-identical to what
    /// [`qf_uf_interpolant`] returns for the same `(A, B)`).
    pub interpolant: TermId,
    /// `A ∧ ¬I`, the conjunction the [`a_refutation`](Self::a_refutation) refutes
    /// (so a consumer can re-derive a Lean-kernel certificate from it).
    pub a_and_not_i: Vec<TermId>,
    /// `I ∧ B`, the conjunction the [`b_refutation`](Self::b_refutation) refutes.
    pub i_and_b: Vec<TermId>,
    /// Alethe congruence refutation of `A ∧ ¬I` (Craig condition 1).
    pub a_refutation: Vec<AletheCommand>,
    /// Alethe congruence refutation of `I ∧ B` (Craig condition 2).
    pub b_refutation: Vec<AletheCommand>,
}

/// Produces a **certified** Craig interpolant for the unsatisfiable conjunctive
/// `QF_UF` (EUF) partition `A = a_assertions`, `B = b_assertions`: the same
/// verified interpolant [`qf_uf_interpolant`] returns, **plus** two congruence
/// certificates — Alethe `eq_congruent` / `eq_transitive` / `resolution`
/// refutations of `A ∧ ¬I` and `I ∧ B` — that an independent checker (Carcara, or
/// the Lean kernel via [`crate::prove_unsat_to_lean_module`]) can accept on its own.
///
/// This is the `Checked`-assurance upgrade of the `Validated` [`qf_uf_interpolant`]:
/// the interpolant was already verify-before-return; here we additionally emit an
/// externally-checkable certificate for each of its two soundness conditions, and
/// return it **only** when both certificates are produced and self-check (through
/// [`axeyum_cnf::check_alethe`] inside the emitter).
///
/// # Boundary
///
/// Only the CONJUNCTIVE EUF slice is certified here (see
/// [`QfUfInterpolantCertificate`]). The certifiable interpolant is a conjunction
/// of equalities over shared terms; both `A ∧ ¬I` and `I ∧ B` are then
/// single-disequality congruence conflicts. This function declines (`Ok(None)`)
/// whenever [`qf_uf_interpolant`] declines, whenever the produced interpolant is
/// the degenerate `⊤`/`⊥` constant (no congruence atoms to refute through the
/// emitter), or whenever either congruence refutation cannot be emitted/validated.
/// A caller that gets `Ok(None)` should fall back to the `Validated`
/// [`qf_uf_interpolant`] path — this function NEVER returns an uncertified
/// interpolant dressed as certified.
///
/// # Errors
///
/// Propagates [`SolverError`] from the shared interpolant builder (which is
/// currently infallible at the `Result` layer; the signature mirrors the LRA path).
pub fn qf_uf_interpolant_certified(
    arena: &mut TermArena,
    a_assertions: &[TermId],
    b_assertions: &[TermId],
) -> Result<Option<QfUfInterpolantCertificate>, SolverError> {
    // 1. The verified interpolant `I` (identical to `qf_uf_interpolant`'s output).
    let Some(interpolant) = build_verified_qf_uf_interpolant(arena, a_assertions, b_assertions)?
    else {
        return Ok(None);
    };

    // 2. Form the two conjunctions whose UNSAT is the two Craig soundness
    //    conditions. `¬I` is peeled so it is a *bare* disequality (or equality
    //    list), keeping each conjunction a single-disequality congruence conflict
    //    the EUF emitter handles: when `I = ¬(x=y)` we use `(x=y)`, else `¬I`.
    let Some(not_interpolant) = negate_interpolant(arena, interpolant) else {
        return Ok(None);
    };
    let mut a_and_not_i: Vec<TermId> = a_assertions.to_vec();
    a_and_not_i.push(not_interpolant);
    let mut i_and_b: Vec<TermId> = Vec::with_capacity(b_assertions.len() + 1);
    i_and_b.push(interpolant);
    i_and_b.extend_from_slice(b_assertions);

    // 3. Emit a self-validated Alethe congruence refutation for each. The emitter
    //    re-checks the proof through `check_alethe` and yields `None` on any doubt
    //    (or when the conjunction is outside its single-disequality slice); we then
    //    decline to the `Validated` path rather than return an uncertified
    //    interpolant. (External Carcara/Lean acceptance is exercised by the
    //    cross-check tests.)
    let Some(a_refutation) = prove_qf_uf_unsat_alethe(arena, &a_and_not_i) else {
        return Ok(None);
    };
    let Some(b_refutation) = prove_qf_uf_unsat_alethe(arena, &i_and_b) else {
        return Ok(None);
    };

    Ok(Some(QfUfInterpolantCertificate {
        interpolant,
        a_and_not_i,
        i_and_b,
        a_refutation,
        b_refutation,
    }))
}

/// Builds the logical negation `¬I` of an EUF interpolant as a *bare* literal the
/// congruence emitter can classify, peeling a double negation: when `I` is
/// `not(inner)` the negation is `inner` itself (avoiding `not(not(inner))`, which
/// [`crate::prove_qf_uf_unsat_alethe`]'s `classify` cannot read), otherwise it is
/// `not(I)`. Returns `None` if the negation term cannot be built.
fn negate_interpolant(arena: &mut TermArena, interpolant: TermId) -> Option<TermId> {
    if let TermNode::App {
        op: Op::BoolNot,
        args,
    } = arena.node(interpolant)
    {
        if args.len() == 1 {
            return Some(args[0]);
        }
    }
    arena.not(interpolant).ok()
}

/// Recursively gathers the equality / disequality literals of a conjunctive
/// Boolean assertion. Returns `None` for any shape outside `and` / `not` over
/// equality atoms (a disjunction, a bare predicate, etc.) so the caller declines.
fn collect_literals(
    arena: &TermArena,
    term: TermId,
    negated: bool,
    side: Side,
    eqs: &mut Vec<(TermId, TermId, Side)>,
    diseqs: &mut Vec<(TermId, TermId, Side)>,
) -> Option<()> {
    match arena.node(term) {
        TermNode::BoolConst(value) => {
            // A literally-true (or `not false`) conjunct is vacuous; a literally-
            // false conjunct is an unsupported degenerate assertion.
            if *value == negated { None } else { Some(()) }
        }
        TermNode::App {
            op: Op::BoolNot,
            args,
        } if args.len() == 1 => collect_literals(arena, args[0], !negated, side, eqs, diseqs),
        TermNode::App {
            op: Op::BoolAnd,
            args,
        } if !negated && args.len() == 2 => {
            collect_literals(arena, args[0], false, side, eqs, diseqs)?;
            collect_literals(arena, args[1], false, side, eqs, diseqs)
        }
        TermNode::App {
            op: Op::Eq, args, ..
        } if args.len() == 2 => {
            if negated {
                diseqs.push((args[0], args[1], side));
            } else {
                eqs.push((args[0], args[1], side));
            }
            Some(())
        }
        _ => None,
    }
}

/// The color of an equality proof (or sub-proof): empty (trivial), a single
/// partition, or mixed (spanning both — not summarizable here).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Color {
    Empty,
    Single(Side),
    Mixed,
}

fn merge_color(acc: Color, next: Color) -> Color {
    match (acc, next) {
        (Color::Mixed, _) | (_, Color::Mixed) => Color::Mixed,
        (Color::Empty, c) | (c, Color::Empty) => c,
        (Color::Single(p), Color::Single(q)) => {
            if p == q {
                Color::Single(p)
            } else {
                Color::Mixed
            }
        }
    }
}

/// Endpoints `(a, b)` of a proof step.
fn endpoints(step: &ProofStep) -> (ENodeId, ENodeId) {
    match step {
        ProofStep::Input { a, b, .. } | ProofStep::Congruence { a, b, .. } => (*a, *b),
    }
}

/// Colors one proof step: an `Input` by its asserting side, a `Congruence` by the
/// common color of its argument sub-proofs.
fn color_step(bridge: &Bridge, step: &ProofStep) -> Color {
    match step {
        ProofStep::Input { reason, .. } => bridge
            .reason_side
            .get(*reason as usize)
            .map_or(Color::Mixed, |&s| Color::Single(s)),
        ProofStep::Congruence { args, .. } => {
            let mut acc = Color::Empty;
            for &(xa, xb) in args {
                acc = merge_color(acc, color_eq(bridge, xa, xb));
                if acc == Color::Mixed {
                    return Color::Mixed;
                }
            }
            acc
        }
    }
}

/// Colors the equality proof between two congruent nodes (recursing through
/// congruence). `a == b` is trivially `Empty`.
fn color_eq(bridge: &Bridge, a: ENodeId, b: ENodeId) -> Color {
    if a == b {
        return Color::Empty;
    }
    let steps = bridge.egraph.explain_steps(a, b);
    let mut acc = Color::Empty;
    for step in &steps {
        acc = merge_color(acc, color_step(bridge, step));
        if acc == Color::Mixed {
            return Color::Mixed;
        }
    }
    acc
}

/// The subterm sets of each partition, for the shared-vocabulary test.
struct SharedTerms {
    a: BTreeSet<TermId>,
    b: BTreeSet<TermId>,
}

impl SharedTerms {
    /// A term is shared iff it occurs (as a subterm) in both partitions.
    fn contains(&self, term: TermId) -> bool {
        self.a.contains(&term) && self.b.contains(&term)
    }
}

/// One oriented proof edge `from → to` with its step (for congruence lowering).
struct Edge<'s> {
    from: ENodeId,
    to: ENodeId,
    step: &'s ProofStep,
}

/// Threads `explain_steps(a, b)` into a single oriented `a → b` chain of edges.
/// Returns `None` if the steps cannot be threaded into a simple `a → b` path.
fn thread<'s>(a: ENodeId, b: ENodeId, steps: &'s [ProofStep]) -> Option<Vec<Edge<'s>>> {
    let mut remaining: Vec<&ProofStep> = steps.iter().collect();
    let mut cur = a;
    let mut out: Vec<Edge<'s>> = Vec::with_capacity(steps.len());
    while !remaining.is_empty() {
        let pos = remaining.iter().position(|st| {
            let (sa, sb) = endpoints(st);
            sa == cur || sb == cur
        })?;
        let step = remaining.remove(pos);
        let (sa, sb) = endpoints(step);
        let (from, to) = if sa == cur { (sa, sb) } else { (sb, sa) };
        out.push(Edge { from, to, step });
        cur = to;
    }
    if cur == b { Some(out) } else { None }
}

/// Summarizes the proof `a = b`, appending to `atoms` the equalities the
/// `summarized` partition contributes, each over shared terms. Maximal
/// same-side segments are emitted as a single equality between their shared
/// endpoints; a non-shared boundary is **lowered** through congruence edges to
/// their argument paths (recursively). Returns `None` (decline) on a mixed-color
/// edge, a non-shared input boundary, or any shape it cannot summarize.
fn summarize(
    bridge: &Bridge,
    arena: &mut TermArena,
    a: ENodeId,
    b: ENodeId,
    summarized: Side,
    shared: &SharedTerms,
    atoms: &mut Vec<TermId>,
) -> Option<()> {
    if a == b {
        return Some(());
    }
    let steps = bridge.egraph.explain_steps(a, b);
    let oriented = thread(a, b, &steps)?;

    // Color each edge, declining on mixed / trivially-empty edges.
    let mut colored: Vec<(usize, Side)> = Vec::with_capacity(oriented.len());
    for (idx, edge) in oriented.iter().enumerate() {
        let side = match color_step(bridge, edge.step) {
            Color::Single(s) => s,
            Color::Empty | Color::Mixed => return None,
        };
        colored.push((idx, side));
    }

    // Walk maximal same-side runs; only the `summarized` side contributes.
    let mut i = 0;
    while i < colored.len() {
        let (_, side) = colored[i];
        let mut j = i + 1;
        while j < colored.len() && colored[j].1 == side {
            j += 1;
        }
        if side == summarized {
            let seg = &oriented[i..j];
            summarize_segment(bridge, arena, seg, summarized, shared, atoms)?;
        }
        i = j;
    }
    Some(())
}

/// Summarizes one maximal `summarized`-colored segment `seg` (oriented edges):
/// emit `x = y` between its shared endpoints, or, when an endpoint is not shared,
/// lower each edge — input edges must have shared endpoints; congruence edges
/// recurse into their argument paths.
fn summarize_segment(
    bridge: &Bridge,
    arena: &mut TermArena,
    seg: &[Edge<'_>],
    summarized: Side,
    shared: &SharedTerms,
    atoms: &mut Vec<TermId>,
) -> Option<()> {
    let x = bridge.term_of(seg.first()?.from)?;
    let y = bridge.term_of(seg.last()?.to)?;
    if shared.contains(x) && shared.contains(y) {
        let atom = arena.eq(x, y).ok()?;
        atoms.push(atom);
        return Some(());
    }
    // Non-shared boundary: lower edge by edge.
    for edge in seg {
        match edge.step {
            ProofStep::Input { .. } => {
                let from = bridge.term_of(edge.from)?;
                let to = bridge.term_of(edge.to)?;
                if !shared.contains(from) || !shared.contains(to) {
                    return None; // an input equality is a leaf — cannot be lowered.
                }
                let atom = arena.eq(from, to).ok()?;
                atoms.push(atom);
            }
            ProofStep::Congruence { args, .. } => {
                for &(xa, xb) in args {
                    summarize(bridge, arena, xa, xb, summarized, shared, atoms)?;
                }
            }
        }
    }
    Some(())
}

/// Conjoins atoms into a single term (`⋀ ∅ = ⊤`). Folds left; a build failure
/// collapses to `⊤` only when no atoms — otherwise the caller's `arena.and`
/// cannot fail for well-sorted Bool atoms.
fn conjoin(arena: &mut TermArena, atoms: &[TermId]) -> TermId {
    let Some((first, rest)) = atoms.split_first() else {
        return arena.bool_const(true);
    };
    let mut acc = *first;
    for &atom in rest {
        match arena.and(acc, atom) {
            Ok(t) => acc = t,
            Err(_) => return arena.bool_const(true),
        }
    }
    acc
}

/// Re-checks the three Craig conditions for `interpolant` over `(A, B)` using the
/// independent `QF_UF` decider. Returns `true` iff all hold.
fn verify_interpolant(
    arena: &mut TermArena,
    a_assertions: &[TermId],
    b_assertions: &[TermId],
    interpolant: TermId,
) -> bool {
    // (3) Vocabulary: every symbol / function used by I appears in both A and B.
    let a_vocab = vocab_of(arena, a_assertions);
    let b_vocab = vocab_of(arena, b_assertions);
    let i_vocab = vocab_of(arena, std::slice::from_ref(&interpolant));
    if !i_vocab
        .iter()
        .all(|item| a_vocab.contains(item) && b_vocab.contains(item))
    {
        return false;
    }

    // (1) A ⇒ I  ≡  A ∧ ¬I unsat.
    let Ok(not_i) = arena.not(interpolant) else {
        return false;
    };
    let mut a_not_i = a_assertions.to_vec();
    a_not_i.push(not_i);
    if !matches!(check_qf_uf(arena, &a_not_i), CheckResult::Unsat) {
        return false;
    }

    // (2) I ∧ B unsat.
    let mut i_and_b = vec![interpolant];
    i_and_b.extend_from_slice(b_assertions);
    matches!(check_qf_uf(arena, &i_and_b), CheckResult::Unsat)
}

/// A vocabulary item: an uninterpreted constant symbol or function symbol.
/// Interpreted operators and logical connectives are not vocabulary (both sides
/// always have them), so they are excluded.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum VocabItem {
    Symbol(usize),
    Func(usize),
}

/// Collects the uninterpreted vocabulary (constant + function symbols) of a set
/// of terms.
fn vocab_of(arena: &TermArena, terms: &[TermId]) -> BTreeSet<VocabItem> {
    let mut out = BTreeSet::new();
    let mut seen = BTreeSet::new();
    for &term in terms {
        collect_vocab(arena, term, &mut out, &mut seen);
    }
    out
}

fn collect_vocab(
    arena: &TermArena,
    term: TermId,
    out: &mut BTreeSet<VocabItem>,
    seen: &mut BTreeSet<TermId>,
) {
    if !seen.insert(term) {
        return;
    }
    match arena.node(term) {
        TermNode::Symbol(s) => {
            out.insert(VocabItem::Symbol(s.index()));
        }
        TermNode::App { op, args } => {
            if let Op::Apply(func) = op {
                out.insert(VocabItem::Func(func.index()));
            }
            for &arg in args {
                collect_vocab(arena, arg, out, seen);
            }
        }
        _ => {}
    }
}

/// Collects every subterm `TermId` appearing in a set of terms.
fn subterms_of(arena: &TermArena, terms: &[TermId]) -> BTreeSet<TermId> {
    let mut out = BTreeSet::new();
    for &term in terms {
        collect_subterms(arena, term, &mut out);
    }
    out
}

fn collect_subterms(arena: &TermArena, term: TermId, out: &mut BTreeSet<TermId>) {
    if !out.insert(term) {
        return;
    }
    if let TermNode::App { args, .. } = arena.node(term) {
        for &arg in args {
            collect_subterms(arena, arg, out);
        }
    }
}

/// A congruence-closure bridge mirroring [`crate::euf_egraph`]'s: every
/// symbol / function / operator / constant gets a distinct `decl`, with a
/// bidirectional term ↔ node map and a per-merge-reason partition tag.
struct Bridge {
    egraph: EGraph,
    node_to_term: HashMap<ENodeId, TermId>,
    term_to_node: HashMap<TermId, ENodeId>,
    decls: HashMap<DeclKey, u32>,
    reason_side: Vec<Side>,
    next_decl: u32,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum DeclKey {
    Symbol(usize),
    Func(usize),
    Op(String),
    Const(String),
}

impl Bridge {
    fn new() -> Self {
        Self {
            egraph: EGraph::new(),
            node_to_term: HashMap::new(),
            term_to_node: HashMap::new(),
            decls: HashMap::new(),
            reason_side: Vec::new(),
            next_decl: 0,
        }
    }

    fn decl(&mut self, key: DeclKey) -> u32 {
        if let Some(&d) = self.decls.get(&key) {
            return d;
        }
        let d = self.next_decl;
        self.next_decl += 1;
        self.decls.insert(key, d);
        d
    }

    fn node_of(&self, term: TermId) -> Option<ENodeId> {
        self.term_to_node.get(&term).copied()
    }

    fn term_of(&self, node: ENodeId) -> Option<TermId> {
        self.node_to_term.get(&node).copied()
    }

    /// Interns `term` (and its subterms) into the e-graph, returning its node.
    /// Returns `None` for a shape it cannot represent.
    fn add_term(&mut self, arena: &TermArena, term: TermId) -> Option<ENodeId> {
        if let Some(&n) = self.term_to_node.get(&term) {
            return Some(n);
        }
        let node = match arena.node(term) {
            TermNode::Symbol(s) => {
                let decl = self.decl(DeclKey::Symbol(s.index()));
                self.egraph.add(decl, &[])
            }
            TermNode::BoolConst(_)
            | TermNode::BvConst { .. }
            | TermNode::WideBvConst(_)
            | TermNode::IntConst(_)
            | TermNode::RealConst(_) => {
                let key = DeclKey::Const(format!("{:?}", arena.node(term)));
                let decl = self.decl(key);
                self.egraph.add(decl, &[])
            }
            TermNode::App { op, args } => {
                let op = *op;
                let args = args.clone();
                let mut child_nodes = Vec::with_capacity(args.len());
                for &a in &args {
                    child_nodes.push(self.add_term(arena, a)?);
                }
                let key = match op {
                    Op::Apply(func) => DeclKey::Func(func.index()),
                    other => DeclKey::Op(format!("{other:?}")),
                };
                let decl = self.decl(key);
                self.egraph.add(decl, &child_nodes)
            }
        };
        self.term_to_node.insert(term, node);
        self.node_to_term.entry(node).or_insert(term);
        Some(node)
    }
}
