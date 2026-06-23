//! Ground EUF Craig interpolation (Track 3, **T3.8.3**).
//!
//! Each test refutes a `QF_UF` conjunction `A ∧ B`, asks [`qf_uf_interpolant`]
//! for an interpolant `I`, and *independently* re-checks `A ⇒ I`, `I ∧ B ⇒ ⊥`,
//! and the shared-vocabulary condition with `check_qf_uf` — so the assurance does
//! not lean on the generator's own internal verification.

use std::collections::BTreeSet;

use axeyum_cnf::check_alethe;
use axeyum_ir::{Assignment, Op, Sort, TermArena, TermId, TermNode, Value, eval};
use axeyum_solver::{
    CheckResult, SatBvBackend, Solver, SolverConfig, check_auto, check_qf_uf, qf_uf_interpolant,
    qf_uf_interpolant_certified,
};

fn con(arena: &mut TermArena, name: &str) -> TermId {
    let s = arena.declare(name, Sort::Int).unwrap();
    arena.var(s)
}

fn eq(arena: &mut TermArena, a: TermId, b: TermId) -> TermId {
    arena.eq(a, b).unwrap()
}

fn neq(arena: &mut TermArena, a: TermId, b: TermId) -> TermId {
    let e = arena.eq(a, b).unwrap();
    arena.not(e).unwrap()
}

fn is_unsat(arena: &mut TermArena, assertions: &[TermId]) -> bool {
    matches!(check_qf_uf(arena, assertions), CheckResult::Unsat)
}

/// Like [`is_unsat`], but routes through the full [`check_auto`] dispatch instead
/// of the EUF-only [`check_qf_uf`] — so it can refute conjunctions whose atoms span
/// theories EUF cannot reason about (e.g. the `≤`/`≥` atoms of an LRA interpolant).
fn is_unsat_auto(arena: &mut TermArena, assertions: &[TermId]) -> bool {
    matches!(
        check_auto(arena, assertions, &SolverConfig::default()),
        Ok(CheckResult::Unsat)
    )
}

/// Vocabulary (uninterpreted symbols + functions) used by a term.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum V {
    Sym(usize),
    Fun(usize),
}

fn vocab(arena: &TermArena, term: TermId, out: &mut BTreeSet<V>, seen: &mut BTreeSet<TermId>) {
    if !seen.insert(term) {
        return;
    }
    match arena.node(term) {
        TermNode::Symbol(s) => {
            out.insert(V::Sym(s.index()));
        }
        TermNode::App { op, args } => {
            if let Op::Apply(f) = op {
                out.insert(V::Fun(f.index()));
            }
            for &a in args {
                vocab(arena, a, out, seen);
            }
        }
        _ => {}
    }
}

fn vocab_of(arena: &TermArena, terms: &[TermId]) -> BTreeSet<V> {
    let mut out = BTreeSet::new();
    let mut seen = BTreeSet::new();
    for &t in terms {
        vocab(arena, t, &mut out, &mut seen);
    }
    out
}

/// Independently verifies that `i` is a Craig interpolant for `(a, b)`.
fn assert_is_interpolant(arena: &mut TermArena, a: &[TermId], b: &[TermId], i: TermId) {
    // (1) A ⇒ I  ≡  A ∧ ¬I unsat.
    let not_i = arena.not(i).unwrap();
    let mut a_not_i = a.to_vec();
    a_not_i.push(not_i);
    assert!(is_unsat(arena, &a_not_i), "A ∧ ¬I must be unsat (A ⇒ I)");

    // (2) I ∧ B unsat.
    let mut i_b = vec![i];
    i_b.extend_from_slice(b);
    assert!(is_unsat(arena, &i_b), "I ∧ B must be unsat");

    // (3) Vocabulary ⊆ shared.
    let av = vocab_of(arena, a);
    let bv = vocab_of(arena, b);
    let iv = vocab_of(arena, std::slice::from_ref(&i));
    for v in &iv {
        assert!(
            av.contains(v) && bv.contains(v),
            "interpolant uses a non-shared symbol"
        );
    }
}

/// Independently verifies that `i` is a Craig interpolant for `(a, b)`, refuting
/// the two implication conditions with the full [`check_auto`] dispatch. Use this
/// when the producing theory is not known to be EUF-only — the façade may return,
/// e.g., an LRA interpolant over `≤`/`≥` atoms that the EUF-only [`is_unsat`]
/// cannot decide. The three Craig conditions are checked in full; only the decider
/// is broadened.
fn assert_is_interpolant_auto(arena: &mut TermArena, a: &[TermId], b: &[TermId], i: TermId) {
    // (1) A ⇒ I  ≡  A ∧ ¬I unsat.
    let not_i = arena.not(i).unwrap();
    let mut a_not_i = a.to_vec();
    a_not_i.push(not_i);
    assert!(
        is_unsat_auto(arena, &a_not_i),
        "A ∧ ¬I must be unsat (A ⇒ I)"
    );

    // (2) I ∧ B unsat.
    let mut i_b = vec![i];
    i_b.extend_from_slice(b);
    assert!(is_unsat_auto(arena, &i_b), "I ∧ B must be unsat");

    // (3) Vocabulary ⊆ shared.
    let av = vocab_of(arena, a);
    let bv = vocab_of(arena, b);
    let iv = vocab_of(arena, std::slice::from_ref(&i));
    for v in &iv {
        assert!(
            av.contains(v) && bv.contains(v),
            "interpolant uses a non-shared symbol"
        );
    }
}

#[test]
fn transitivity_diseq_in_b() {
    // A: a=b, b=c ; B: a≠c.  I should be a=c (shared a,c).
    let mut arena = TermArena::new();
    let (a, b, c) = (
        con(&mut arena, "a"),
        con(&mut arena, "b"),
        con(&mut arena, "c"),
    );
    let a_eq_b = eq(&mut arena, a, b);
    let b_eq_c = eq(&mut arena, b, c);
    let a_ne_c = neq(&mut arena, a, c);

    let i = qf_uf_interpolant(&mut arena, &[a_eq_b, b_eq_c], &[a_ne_c])
        .expect("decides")
        .expect("EUF interpolant exists");
    assert_is_interpolant(&mut arena, &[a_eq_b, b_eq_c], &[a_ne_c], i);
}

#[test]
fn transitivity_diseq_in_a() {
    // A: a≠c ; B: a=b, b=c.  I should be ¬(a=c).
    let mut arena = TermArena::new();
    let (a, b, c) = (
        con(&mut arena, "a"),
        con(&mut arena, "b"),
        con(&mut arena, "c"),
    );
    let a_ne_c = neq(&mut arena, a, c);
    let a_eq_b = eq(&mut arena, a, b);
    let b_eq_c = eq(&mut arena, b, c);

    let i = qf_uf_interpolant(&mut arena, &[a_ne_c], &[a_eq_b, b_eq_c])
        .expect("decides")
        .expect("EUF interpolant exists");
    assert_is_interpolant(&mut arena, &[a_ne_c], &[a_eq_b, b_eq_c], i);
}

#[test]
fn mixed_chain_shared_boundary() {
    // A: a=b ; B: b=c, a≠c.  The A-segment summary is a=b (b is shared).
    let mut arena = TermArena::new();
    let (a, b, c) = (
        con(&mut arena, "a"),
        con(&mut arena, "b"),
        con(&mut arena, "c"),
    );
    let a_eq_b = eq(&mut arena, a, b);
    let b_eq_c = eq(&mut arena, b, c);
    let a_ne_c = neq(&mut arena, a, c);

    let i = qf_uf_interpolant(&mut arena, &[a_eq_b], &[b_eq_c, a_ne_c])
        .expect("decides")
        .expect("EUF interpolant exists");
    assert_is_interpolant(&mut arena, &[a_eq_b], &[b_eq_c, a_ne_c], i);
}

#[test]
fn congruence_lowers_to_argument_equality() {
    // A: a=b ; B: f(a)≠f(b).  f is B-only, so the interpolant must lower the
    // congruence f(a)=f(b) to the shared argument equality a=b.
    let mut arena = TermArena::new();
    let (a, b) = (con(&mut arena, "a"), con(&mut arena, "b"));
    let f = arena.declare_fun("f", &[Sort::Int], Sort::Int).unwrap();
    let fa = arena.apply(f, &[a]).unwrap();
    let fb = arena.apply(f, &[b]).unwrap();
    let a_eq_b = eq(&mut arena, a, b);
    let fa_ne_fb = neq(&mut arena, fa, fb);

    let i = qf_uf_interpolant(&mut arena, &[a_eq_b], &[fa_ne_fb])
        .expect("decides")
        .expect("EUF interpolant exists");
    assert_is_interpolant(&mut arena, &[a_eq_b], &[fa_ne_fb], i);
}

#[test]
fn nested_congruence_lowers() {
    // A: a=b ; B: g(f(a)) ≠ g(f(b)).  Lower twice to a=b.
    let mut arena = TermArena::new();
    let (a, b) = (con(&mut arena, "a"), con(&mut arena, "b"));
    let f = arena.declare_fun("f", &[Sort::Int], Sort::Int).unwrap();
    let g = arena.declare_fun("g", &[Sort::Int], Sort::Int).unwrap();
    let fa = arena.apply(f, &[a]).unwrap();
    let fb = arena.apply(f, &[b]).unwrap();
    let gfa = arena.apply(g, &[fa]).unwrap();
    let gfb = arena.apply(g, &[fb]).unwrap();
    let a_eq_b = eq(&mut arena, a, b);
    let gfa_ne_gfb = neq(&mut arena, gfa, gfb);

    let itp = qf_uf_interpolant(&mut arena, &[a_eq_b], &[gfa_ne_gfb])
        .expect("decides")
        .expect("EUF interpolant exists");
    assert_is_interpolant(&mut arena, &[a_eq_b], &[gfa_ne_gfb], itp);
}

#[test]
fn congruence_with_shared_function() {
    // A: a=b ; B: f(a)≠f(b), where f is used in BOTH (shared). Interpolant can be
    // either f(a)=f(b) or a=b; both are valid — we just check it verifies.
    let mut arena = TermArena::new();
    let (a, b, p) = (
        con(&mut arena, "a"),
        con(&mut arena, "b"),
        con(&mut arena, "p"),
    );
    let f = arena.declare_fun("f", &[Sort::Int], Sort::Int).unwrap();
    let fa = arena.apply(f, &[a]).unwrap();
    let fb = arena.apply(f, &[b]).unwrap();
    let fp = arena.apply(f, &[p]).unwrap();
    // A also mentions f (via a trivial f(a)=f(p) ∨ ... — keep it simple: A has f(a)).
    let a_eq_b = eq(&mut arena, a, b);
    let fp_eq_fp = eq(&mut arena, fp, fa); // ties f and a into A's vocabulary
    let fa_ne_fb = neq(&mut arena, fa, fb);

    let itp = qf_uf_interpolant(&mut arena, &[a_eq_b, fp_eq_fp], &[fa_ne_fb])
        .expect("decides")
        .expect("EUF interpolant exists");
    assert_is_interpolant(&mut arena, &[a_eq_b, fp_eq_fp], &[fa_ne_fb], itp);
}

#[test]
fn solver_facade_returns_a_verified_interpolant() {
    // The Solver façade dispatches LRA → LIA → EUF → … in turn. The constants are
    // `Sort::Int`, so the equalities `a=b, b=c, a≠c` are decidable arithmetic and the
    // *first* theory — LRA — produces (and self-verifies) a valid interpolant of the
    // form `c ≤ a ∧ a ≤ c` (i.e. `a = c`) over the shared `{a, c}`; it never reaches
    // the EUF fall-through. The point this test makes is the façade-level invariant:
    // `Solver::interpolant` returns only *verified* interpolants. We re-check all three
    // Craig conditions independently with `check_auto`, the full decider — `check_qf_uf`
    // alone cannot reason about the `≤` atoms LRA emits. Active assertions
    // [a=b, b=c, a≠c]; A = {0, 1}.
    let mut arena = TermArena::new();
    let (a, b, c) = (
        con(&mut arena, "a"),
        con(&mut arena, "b"),
        con(&mut arena, "c"),
    );
    let a_eq_b = eq(&mut arena, a, b);
    let b_eq_c = eq(&mut arena, b, c);
    let a_ne_c = neq(&mut arena, a, c);

    let mut solver = Solver::new(SatBvBackend::new());
    solver.assert(a_eq_b);
    solver.assert(b_eq_c);
    solver.assert(a_ne_c);

    let i = solver
        .interpolant(&mut arena, &[0, 1])
        .expect("decides")
        .expect("interpolant via façade");
    assert_is_interpolant_auto(&mut arena, &[a_eq_b, b_eq_c], &[a_ne_c], i);
}

#[test]
fn satisfiable_has_no_interpolant() {
    // A: a=b ; B: c=d.  Satisfiable — decline.
    let mut arena = TermArena::new();
    let (a, b, c, d) = (
        con(&mut arena, "a"),
        con(&mut arena, "b"),
        con(&mut arena, "c"),
        con(&mut arena, "d"),
    );
    let a_eq_b = eq(&mut arena, a, b);
    let c_eq_d = eq(&mut arena, c, d);
    assert!(
        qf_uf_interpolant(&mut arena, &[a_eq_b], &[c_eq_d])
            .expect("decides")
            .is_none(),
        "a satisfiable conjunction must yield no interpolant"
    );
}

#[test]
fn b_alone_unsat_yields_true() {
    // A: (empty) ; B: a=b ∧ a≠b.  Interpolant ⊤.
    let mut arena = TermArena::new();
    let (a, b) = (con(&mut arena, "a"), con(&mut arena, "b"));
    let a_eq_b = eq(&mut arena, a, b);
    let a_ne_b = neq(&mut arena, a, b);

    let i = qf_uf_interpolant(&mut arena, &[], &[a_eq_b, a_ne_b])
        .expect("decides")
        .expect("interpolant exists");
    // Degenerate ⊤: A ⇒ ⊤ trivially, ⊤ ∧ B = B unsat, empty vocabulary.
    assert_eq!(
        eval(&arena, i, &Assignment::new()).unwrap(),
        Value::Bool(true),
        "B-alone-unsat interpolant must be ⊤"
    );
    assert!(is_unsat(&mut arena, &[a_eq_b, a_ne_b]), "⊤ ∧ B = B unsat");
}

#[test]
fn a_alone_unsat_yields_false() {
    // A: a=b ∧ a≠b ; B: (empty).  Interpolant ⊥.
    let mut arena = TermArena::new();
    let (a, b) = (con(&mut arena, "a"), con(&mut arena, "b"));
    let a_eq_b = eq(&mut arena, a, b);
    let a_ne_b = neq(&mut arena, a, b);

    let i = qf_uf_interpolant(&mut arena, &[a_eq_b, a_ne_b], &[])
        .expect("decides")
        .expect("interpolant exists");
    // Degenerate ⊥: A ⇒ ⊥ (A unsat), ⊥ ∧ B unsat, empty vocabulary.
    assert_eq!(
        eval(&arena, i, &Assignment::new()).unwrap(),
        Value::Bool(false),
        "A-alone-unsat interpolant must be ⊥"
    );
    assert!(is_unsat(&mut arena, &[a_eq_b, a_ne_b]), "A unsat ⇒ A ⇒ ⊥");
}

// --- Certified conjunctive EUF interpolation (`qf_uf_interpolant_certified`) ---

/// The certified path returns the SAME verified interpolant as `qf_uf_interpolant`,
/// re-passes the three Craig conditions, and carries two congruence refutations that
/// BOTH self-check through the in-tree `check_alethe` (the counterpart to the
/// external Carcara/Lean acceptance the cross-check suites exercise).
#[test]
fn certified_euf_interpolant_carries_two_self_checked_congruence_refutations() {
    // A: a=b, b=c ; B: a≠c.  I = (a=c), a positive equality conjunction (diseq in B).
    let mut arena = TermArena::new();
    let (a, b, c) = (
        con(&mut arena, "a"),
        con(&mut arena, "b"),
        con(&mut arena, "c"),
    );
    let a_eq_b = eq(&mut arena, a, b);
    let b_eq_c = eq(&mut arena, b, c);
    let a_ne_c = neq(&mut arena, a, c);

    // Byte-identical interpolant to the Validated path.
    let validated = qf_uf_interpolant(&mut arena, &[a_eq_b, b_eq_c], &[a_ne_c])
        .expect("decides")
        .expect("interpolant exists");
    let cert = qf_uf_interpolant_certified(&mut arena, &[a_eq_b, b_eq_c], &[a_ne_c])
        .expect("decides")
        .expect("a certified interpolant exists for an unsat EUF conjunction");
    assert_eq!(
        cert.interpolant, validated,
        "the certified interpolant must equal the Validated qf_uf_interpolant output"
    );

    // The three Craig conditions still hold for the returned interpolant.
    assert_is_interpolant(&mut arena, &[a_eq_b, b_eq_c], &[a_ne_c], cert.interpolant);

    // The two carried refutations are genuine congruence proofs deriving the empty
    // clause — accepted by the in-tree checker (external Carcara/Lean acceptance is
    // asserted in `carcara_crosscheck`/`lean_crosscheck`).
    assert_eq!(
        check_alethe(&cert.a_refutation),
        Ok(true),
        "the A ∧ ¬I refutation (Craig condition 1) must self-check"
    );
    assert_eq!(
        check_alethe(&cert.b_refutation),
        Ok(true),
        "the I ∧ B refutation (Craig condition 2) must self-check"
    );

    // The carried conjunctions are exactly A ∧ ¬I and I ∧ B (each genuinely unsat).
    assert!(
        is_unsat(&mut arena, &cert.a_and_not_i),
        "A ∧ ¬I must be unsat"
    );
    assert!(is_unsat(&mut arena, &cert.i_and_b), "I ∧ B must be unsat");
}

/// The disequality-in-`A` case: `I = ¬(a=c)`. `¬I` is *peeled* back to the bare
/// equality `(a=c)` so `A ∧ ¬I` stays a single-disequality congruence conflict the
/// emitter handles — both refutations self-check.
#[test]
fn certified_euf_interpolant_negated_interpolant_diseq_in_a() {
    // A: a≠c ; B: a=b, b=c.  I = ¬(a=c).
    let mut arena = TermArena::new();
    let (a, b, c) = (
        con(&mut arena, "a"),
        con(&mut arena, "b"),
        con(&mut arena, "c"),
    );
    let a_ne_c = neq(&mut arena, a, c);
    let a_eq_b = eq(&mut arena, a, b);
    let b_eq_c = eq(&mut arena, b, c);

    let cert = qf_uf_interpolant_certified(&mut arena, &[a_ne_c], &[a_eq_b, b_eq_c])
        .expect("decides")
        .expect("certified interpolant exists");
    assert_is_interpolant(&mut arena, &[a_ne_c], &[a_eq_b, b_eq_c], cert.interpolant);
    assert_eq!(check_alethe(&cert.a_refutation), Ok(true));
    assert_eq!(check_alethe(&cert.b_refutation), Ok(true));
}

/// A congruence interpolant (shared `f(a)`/`f(b)`): `A: a=b`, `B: f(a)≠f(b)`. The
/// interpolant `f(a)=f(b)` is a positive equality over shared terms; both Craig
/// refutations are congruence conflicts and self-check.
#[test]
fn certified_euf_interpolant_congruence() {
    let mut arena = TermArena::new();
    let (a, b) = (con(&mut arena, "a"), con(&mut arena, "b"));
    let f = arena
        .declare_fun("f", &[Sort::Int], Sort::Int)
        .expect("declare_fun");
    let fa = arena.apply(f, &[a]).unwrap();
    let fb = arena.apply(f, &[b]).unwrap();
    let a_eq_b = eq(&mut arena, a, b);
    let fa_ne_fb = neq(&mut arena, fa, fb);

    let cert = qf_uf_interpolant_certified(&mut arena, &[a_eq_b], &[fa_ne_fb])
        .expect("decides")
        .expect("certified interpolant exists");
    assert_is_interpolant(&mut arena, &[a_eq_b], &[fa_ne_fb], cert.interpolant);
    assert_eq!(check_alethe(&cert.a_refutation), Ok(true));
    assert_eq!(check_alethe(&cert.b_refutation), Ok(true));
}

/// A satisfiable conjunction has no interpolant, so the certified path declines
/// (`Ok(None)`) — the caller falls back to `qf_uf_interpolant`, which also declines.
/// Nothing is dressed up as certified.
#[test]
fn certified_euf_interpolant_declines_on_satisfiable() {
    // A: a=b ; B: c=d — satisfiable, so neither path yields an interpolant.
    let mut arena = TermArena::new();
    let (a, b, c, d) = (
        con(&mut arena, "a"),
        con(&mut arena, "b"),
        con(&mut arena, "c"),
        con(&mut arena, "d"),
    );
    let a_eq_b = eq(&mut arena, a, b);
    let c_eq_d = eq(&mut arena, c, d);

    assert!(
        qf_uf_interpolant_certified(&mut arena, &[a_eq_b], &[c_eq_d])
            .expect("decides")
            .is_none(),
        "a satisfiable A ∧ B must yield no certified interpolant"
    );
    assert!(
        qf_uf_interpolant(&mut arena, &[a_eq_b], &[c_eq_d])
            .expect("decides")
            .is_none(),
        "the Validated fallback must also decline"
    );
}

/// The degenerate `⊤` interpolant (B alone unsat) is a bare Bool constant with no
/// congruence atoms to refute, so the certified path declines (`Ok(None)`) and the
/// caller falls back to the `Validated` `qf_uf_interpolant`, which still returns the
/// `⊤` interpolant. This documents the conjunctive-only boundary.
#[test]
fn certified_euf_interpolant_declines_on_degenerate_top() {
    // A: (empty) ; B: a=b ∧ a≠b — B alone unsat, interpolant ⊤.
    let mut arena = TermArena::new();
    let (a, b) = (con(&mut arena, "a"), con(&mut arena, "b"));
    let a_eq_b = eq(&mut arena, a, b);
    let a_ne_b = neq(&mut arena, a, b);

    assert!(
        qf_uf_interpolant_certified(&mut arena, &[], &[a_eq_b, a_ne_b])
            .expect("decides")
            .is_none(),
        "the degenerate ⊤ interpolant is out of the certified slice"
    );
    // The Validated path still yields the ⊤ interpolant.
    assert!(
        qf_uf_interpolant(&mut arena, &[], &[a_eq_b, a_ne_b])
            .expect("decides")
            .is_some(),
        "the Validated fallback still produces the ⊤ interpolant"
    );
}

/// TAMPER (the self-check has teeth): corrupting a carried congruence refutation's
/// derived equality makes the in-tree `check_alethe` REJECT it. A wrong certificate
/// cannot masquerade as valid — a bug surfaces as a rejection, never an unsound
/// accept. (The external-Carcara analogue of this tamper is in `carcara_crosscheck`.)
#[test]
fn tampered_certified_euf_refutation_is_rejected() {
    use axeyum_cnf::{AletheCommand, AletheLit, AletheTerm};
    let mut arena = TermArena::new();
    let (a, b, c) = (
        con(&mut arena, "a"),
        con(&mut arena, "b"),
        con(&mut arena, "c"),
    );
    let a_eq_b = eq(&mut arena, a, b);
    let b_eq_c = eq(&mut arena, b, c);
    let a_ne_c = neq(&mut arena, a, c);
    let cert = qf_uf_interpolant_certified(&mut arena, &[a_eq_b, b_eq_c], &[a_ne_c])
        .expect("decides")
        .expect("certified interpolant exists");

    // The genuine refutation passes.
    assert_eq!(check_alethe(&cert.a_refutation), Ok(true));

    // Tamper: rewrite a non-`assume` derived step's clause to a bogus reflexive
    // equality `(= a a)` that its premises do not entail and that no longer chains
    // to the empty clause, so `check_alethe` rejects the proof.
    let mut tampered = cert.a_refutation.clone();
    let mut patched = false;
    for cmd in &mut tampered {
        if let AletheCommand::Step { clause, .. } = cmd {
            if !clause.is_empty() {
                let bogus = AletheTerm::App(
                    "=".to_owned(),
                    vec![
                        AletheTerm::Const("a".to_owned()),
                        AletheTerm::Const("a".to_owned()),
                    ],
                );
                *clause = vec![AletheLit {
                    atom: bogus,
                    negated: false,
                }];
                patched = true;
                break;
            }
        }
    }
    assert!(patched, "expected a derivable step to tamper");
    assert_ne!(
        check_alethe(&tampered),
        Ok(true),
        "a tampered congruence refutation must NOT self-check"
    );
}
