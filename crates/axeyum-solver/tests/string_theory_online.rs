//! Census-shape gates for the online CDCL(T) string theory (P1.5 slice b):
//! [`check_qf_s_online_cdclt`].
//!
//! The measured target is the class of **Boolean-structured word problems the
//! one-shot word side channel cannot touch**. The side channel is all-or-nothing
//! over a *top-level conjunction*; the census `r1_QF_S_str002` family wraps its
//! word equalities in `or` / negation:
//!
//! ```text
//! (assert (or (= x (str.++ y "aa")) (= x (str.++ y "bb"))))
//! (assert (= x (str.++ y "cc")))
//! ```
//!
//! Each disjunct, conjoined with the second assertion, is a **theory** conflict —
//! a constant clash after the shared prefix `y` — while the Boolean skeleton alone
//! `(P ∨ Q) ∧ R` is satisfiable. Only theory conflicts driving the Boolean search
//! to exhaustion decide these `unsat`; the sat variants are decided `sat` with a
//! replay-checked model. The theory-driven `unsat` is certified inside the entry
//! point (`StringTheory::assert_conflicts_certified`), so a passing `unsat` here is
//! a *checked-derivation* `unsat`.
#![cfg(feature = "full")]
#![allow(clippy::many_single_char_names, clippy::similar_names)]

use axeyum_ir::{ArraySortKey, Sort, TermArena, TermId};
use axeyum_solver::{CheckResult, SolverConfig, check_qf_s_online_cdclt};

const ELEM: ArraySortKey = ArraySortKey::BitVec(8);

fn seq_sort() -> Sort {
    Sort::Seq(ELEM)
}

fn var(arena: &mut TermArena, name: &str) -> TermId {
    let s = arena.declare(name, seq_sort()).expect("declare seq var");
    arena.var(s)
}

/// A byte-string literal as a right-associated `seq.unit` block (`""` → ε).
fn lit(arena: &mut TermArena, s: &str) -> TermId {
    let mut acc: Option<TermId> = None;
    for &b in s.as_bytes().iter().rev() {
        let c = arena.bv_const(8, u128::from(b)).expect("char const");
        let u = arena.seq_unit(c).expect("seq.unit");
        acc = Some(match acc {
            None => u,
            Some(rest) => arena.seq_concat(u, rest).expect("str.++"),
        });
    }
    acc.unwrap_or_else(|| arena.seq_empty(ELEM))
}

fn cat(arena: &mut TermArena, a: TermId, b: TermId) -> TermId {
    arena.seq_concat(a, b).expect("str.++")
}

fn eq(arena: &mut TermArena, a: TermId, b: TermId) -> TermId {
    arena.eq(a, b).expect("=")
}

fn not(arena: &mut TermArena, a: TermId) -> TermId {
    arena.not(a).expect("not")
}

fn or(arena: &mut TermArena, a: TermId, b: TermId) -> TermId {
    arena.or(a, b).expect("or")
}

fn and(arena: &mut TermArena, a: TermId, b: TermId) -> TermId {
    arena.and(a, b).expect("and")
}

fn decide(arena: &mut TermArena, assertions: &[TermId]) -> CheckResult {
    check_qf_s_online_cdclt(arena, assertions, &SolverConfig::default())
}

// ---------- census-shape UNSAT: disjunction + theory constant clash ----------

#[test]
fn disjunction_of_constant_prefixes_clashes_unsat() {
    // (or (= x (y ++ "aa")) (= x (y ++ "bb"))) ∧ (= x (y ++ "cc"))
    // Each disjunct + the conjunct is a suffix constant clash after the shared y;
    // the skeleton (P ∨ Q) ∧ R is Boolean-SAT — only the theory closes it.
    let mut arena = TermArena::new();
    let x = var(&mut arena, "x");
    let y = var(&mut arena, "y");
    let yaa = {
        let l = lit(&mut arena, "aa");
        cat(&mut arena, y, l)
    };
    let ybb = {
        let l = lit(&mut arena, "bb");
        cat(&mut arena, y, l)
    };
    let ycc = {
        let l = lit(&mut arena, "cc");
        cat(&mut arena, y, l)
    };
    let p = eq(&mut arena, x, yaa);
    let q = eq(&mut arena, x, ybb);
    let r = eq(&mut arena, x, ycc);
    let disj = or(&mut arena, p, q);
    assert_eq!(decide(&mut arena, &[disj, r]), CheckResult::Unsat);
}

#[test]
fn disjunction_of_bare_constants_clashes_unsat() {
    // (or (= x "a") (= x "b")) ∧ (= x "c") — two distinct-constant clashes.
    let mut arena = TermArena::new();
    let x = var(&mut arena, "x");
    let a = lit(&mut arena, "a");
    let b = lit(&mut arena, "b");
    let c = lit(&mut arena, "c");
    let p = eq(&mut arena, x, a);
    let q = eq(&mut arena, x, b);
    let r = eq(&mut arena, x, c);
    let disj = or(&mut arena, p, q);
    assert_eq!(decide(&mut arena, &[disj, r]), CheckResult::Unsat);
}

#[test]
fn nested_disjunction_all_branches_clash_unsat() {
    // (or (or (= x "a") (= x "b")) (= x "c")) ∧ (= x "d") — three branches, each a clash.
    let mut arena = TermArena::new();
    let x = var(&mut arena, "x");
    let a = lit(&mut arena, "a");
    let b = lit(&mut arena, "b");
    let c = lit(&mut arena, "c");
    let d = lit(&mut arena, "d");
    let pa = eq(&mut arena, x, a);
    let pb = eq(&mut arena, x, b);
    let pc = eq(&mut arena, x, c);
    let pd = eq(&mut arena, x, d);
    let ab = or(&mut arena, pa, pb);
    let abc = or(&mut arena, ab, pc);
    assert_eq!(decide(&mut arena, &[abc, pd]), CheckResult::Unsat);
}

#[test]
fn disjunction_with_negated_theory_equality_unsat() {
    // (or (= x (y ++ "a")) (= z (y ++ "a"))) ∧ (= x (y ++ "a")) ∧ (= z (y ++ "a"))
    //  ∧ (not (= x z))
    // x and z both reduce to y ++ "a" so x ≈ z, contradicting the disequality. The
    // leading `or` is redundant with the conjuncts but forces the CDCL(T) route.
    let mut arena = TermArena::new();
    let x = var(&mut arena, "x");
    let y = var(&mut arena, "y");
    let z = var(&mut arena, "z");
    let ya1 = {
        let l = lit(&mut arena, "a");
        cat(&mut arena, y, l)
    };
    let ya2 = {
        let l = lit(&mut arena, "a");
        cat(&mut arena, y, l)
    };
    let ya3 = {
        let l = lit(&mut arena, "a");
        cat(&mut arena, y, l)
    };
    let p = eq(&mut arena, x, ya1);
    let q = eq(&mut arena, z, ya2);
    let r = eq(&mut arena, z, ya3);
    let disj = or(&mut arena, p, q);
    let xz = eq(&mut arena, x, z);
    let nxz = not(&mut arena, xz);
    assert_eq!(decide(&mut arena, &[disj, p, r, nxz]), CheckResult::Unsat);
}

// ---------- census-shape SAT: the satisfiable disjunct, replay-checked ----------

#[test]
fn disjunction_with_a_consistent_branch_sat() {
    // (or (= x (y ++ "aa")) (= x (y ++ "bb"))) ∧ (= x (y ++ "aa")) — branch 1 holds.
    let mut arena = TermArena::new();
    let x = var(&mut arena, "x");
    let y = var(&mut arena, "y");
    let yaa1 = {
        let l = lit(&mut arena, "aa");
        cat(&mut arena, y, l)
    };
    let ybb = {
        let l = lit(&mut arena, "bb");
        cat(&mut arena, y, l)
    };
    let yaa2 = {
        let l = lit(&mut arena, "aa");
        cat(&mut arena, y, l)
    };
    let p = eq(&mut arena, x, yaa1);
    let q = eq(&mut arena, x, ybb);
    let r = eq(&mut arena, x, yaa2);
    let disj = or(&mut arena, p, q);
    assert!(
        matches!(decide(&mut arena, &[disj, r]), CheckResult::Sat(_)),
        "the consistent-branch disjunction must decide sat with a replaying model"
    );
}

#[test]
fn bare_constant_disjunction_consistent_branch_sat() {
    // (or (= x "a") (= x "b")) ∧ (= x "a").
    let mut arena = TermArena::new();
    let x = var(&mut arena, "x");
    let a = lit(&mut arena, "a");
    let b = lit(&mut arena, "b");
    let a2 = lit(&mut arena, "a");
    let p = eq(&mut arena, x, a);
    let q = eq(&mut arena, x, b);
    let r = eq(&mut arena, x, a2);
    let disj = or(&mut arena, p, q);
    assert!(matches!(
        decide(&mut arena, &[disj, r]),
        CheckResult::Sat(_)
    ));
}

#[test]
fn conjunction_of_word_equalities_sat_with_replay() {
    // A plain conjunction the theory keeps consistent: x = y ++ "a", z = "b".
    let mut arena = TermArena::new();
    let x = var(&mut arena, "x");
    let y = var(&mut arena, "y");
    let z = var(&mut arena, "z");
    let ya = {
        let l = lit(&mut arena, "a");
        cat(&mut arena, y, l)
    };
    let bconst = lit(&mut arena, "b");
    let e1 = eq(&mut arena, x, ya);
    let e2 = eq(&mut arena, z, bconst);
    assert!(matches!(decide(&mut arena, &[e1, e2]), CheckResult::Sat(_)));
}

// ---------- soundness sweep: no adversarial UNSAT seed is ever sat ----------

/// Builds every census-shape UNSAT instance in a fresh arena. Each is a
/// theory-coupled contradiction under Boolean structure.
fn adversarial_unsat_instances() -> Vec<(TermArena, Vec<TermId>)> {
    let mut out = Vec::new();

    // suffix clash disjunction
    {
        let mut a = TermArena::new();
        let x = var(&mut a, "x");
        let y = var(&mut a, "y");
        let yaa = {
            let l = lit(&mut a, "aa");
            cat(&mut a, y, l)
        };
        let ybb = {
            let l = lit(&mut a, "bb");
            cat(&mut a, y, l)
        };
        let ycc = {
            let l = lit(&mut a, "cc");
            cat(&mut a, y, l)
        };
        let p = eq(&mut a, x, yaa);
        let q = eq(&mut a, x, ybb);
        let r = eq(&mut a, x, ycc);
        let d = or(&mut a, p, q);
        out.push((a, vec![d, r]));
    }

    // bare-constant disjunction
    {
        let mut a = TermArena::new();
        let x = var(&mut a, "x");
        let la = lit(&mut a, "a");
        let lb = lit(&mut a, "b");
        let lc = lit(&mut a, "c");
        let p = eq(&mut a, x, la);
        let q = eq(&mut a, x, lb);
        let r = eq(&mut a, x, lc);
        let d = or(&mut a, p, q);
        out.push((a, vec![d, r]));
    }

    // and-of-negations plus a disjunction (P ∨ Q) ∧ (¬P') where P' clashes
    {
        let mut a = TermArena::new();
        let x = var(&mut a, "x");
        let la = lit(&mut a, "a");
        let lb = lit(&mut a, "b");
        let lc = lit(&mut a, "c");
        let la2 = lit(&mut a, "a");
        let lb2 = lit(&mut a, "b");
        let p = eq(&mut a, x, la);
        let q = eq(&mut a, x, lb);
        let r = eq(&mut a, x, lc);
        let eqa = eq(&mut a, x, la2);
        let na = not(&mut a, eqa);
        let eqb = eq(&mut a, x, lb2);
        let nb = not(&mut a, eqb);
        let d = or(&mut a, p, q);
        let conj = and(&mut a, na, nb);
        // (P ∨ Q) ∧ ¬P ∧ ¬Q ∧ R — Boolean-unsat too, but must never be sat.
        out.push((a, vec![d, conj, r]));
    }

    out
}

#[test]
fn no_adversarial_unsat_instance_is_ever_sat() {
    for (mut arena, assertions) in adversarial_unsat_instances() {
        match decide(&mut arena, &assertions) {
            CheckResult::Sat(model) => panic!(
                "WRONG SAT on an adversarial UNSAT instance — a soundness bug.\nmodel: {model:?}"
            ),
            CheckResult::Unsat | CheckResult::Unknown(_) => {}
        }
    }
}

// ---------- scope gate: out-of-fragment queries decline to Unknown ----------

#[test]
fn non_sequence_equality_declines_to_unknown() {
    // A bit-vector equality is outside the QF_S online scope.
    let mut arena = TermArena::new();
    let a = arena.bv_var("a", 8).expect("bv a");
    let b = arena.bv_var("b", 8).expect("bv b");
    let e = arena.eq(a, b).expect("=");
    assert!(matches!(decide(&mut arena, &[e]), CheckResult::Unknown(_)));
}
