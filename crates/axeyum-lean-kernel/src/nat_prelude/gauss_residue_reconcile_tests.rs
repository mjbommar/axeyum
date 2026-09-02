//! Tests for
//! [`nat_prelude::gauss_residue_reconcile`](super::gauss_residue_reconcile).
//!
//! Three kinds of check:
//!
//! 1. **Concrete instantiation with every aggregate evaluated to a numeral.**
//!    `leastResidue`/`gaussSignNeg`/`gaussFold` are `mod`/`ble`/`sub`
//!    composites, so at numerals they reduce; each of the four sums is
//!    checked against a number recomputed in Rust, not merely against the
//!    other side of the identity — two stuck aggregates would satisfy that.
//! 2. **Three wrong-but-well-typed readings, each REFUTED numerically** at
//!    one of these instances: dropping the doubling, doubling the
//!    complement's fold sum instead, and conditioning the least residues
//!    rather than the folds. Each is a statement the kernel would accept as
//!    a type; each is false at `(pp, a, m) = (7, 3, 3)`.
//! 3. **The declared type, pinned character for character**, and the axiom
//!    footprint.
//!
//! The instances deliberately include a COMPOSITE, EVEN modulus (`pp = 4`)
//! and a NON-COPRIME pair (`pp = 3`, `a = 3`), because the theorem claims to
//! need neither primality nor coprimality. A version that secretly did would
//! still pass a test suite drawn only from odd primes.

use crate::expr::ExprId;
use crate::{Kernel, NatOps, NatPrelude, NatState, build_nat_prelude};

struct Fixture {
    k: Kernel,
    p: NatPrelude,
    st: NatState,
}

impl NatOps for Fixture {
    fn kernel(&mut self) -> &mut Kernel {
        &mut self.k
    }

    fn nat_state(&mut self) -> &mut NatState {
        &mut self.st
    }
}

/// `leastResidue pp a k`, `gaussSignNeg pp a k` and `gaussFold pp a k`
/// recomputed in Rust straight from their definitions, so no expectation
/// below is inherited from an ADR.
fn residue(pp: u32, a: u32, k: u32) -> u32 {
    (a * k) % pp
}

fn sign_neg(pp: u32, a: u32, k: u32) -> bool {
    pp / 2 + 1 <= residue(pp, a, k)
}

fn fold(pp: u32, a: u32, k: u32) -> u32 {
    let r = residue(pp, a, k);
    if sign_neg(pp, a, k) { pp - r } else { r }
}

/// The five aggregates the identity relates, at one-based indices `1..=m`:
/// `(Σ residue, Σ fold, Σ_{sign} fold, Σ_{¬sign} fold, negative count)`.
struct Sums {
    residues: u32,
    folds: u32,
    negative_folds: u32,
    positive_folds: u32,
    negative_residues: u32,
    count: u32,
}

fn sums(pp: u32, a: u32, m: u32) -> Sums {
    let ks = 1..=m;
    Sums {
        residues: ks.clone().map(|k| residue(pp, a, k)).sum(),
        folds: ks.clone().map(|k| fold(pp, a, k)).sum(),
        negative_folds: ks
            .clone()
            .filter(|&k| sign_neg(pp, a, k))
            .map(|k| fold(pp, a, k))
            .sum(),
        positive_folds: ks
            .clone()
            .filter(|&k| !sign_neg(pp, a, k))
            .map(|k| fold(pp, a, k))
            .sum(),
        negative_residues: ks
            .clone()
            .filter(|&k| sign_neg(pp, a, k))
            .map(|k| residue(pp, a, k))
            .sum(),
        count: u32::try_from(ks.filter(|&k| sign_neg(pp, a, k)).count()).expect("the count fits"),
    }
}

/// The instances used below: `(ap, a, m)` with `pp = ap + 1`.
const INSTANCES: [(u32, u32, u32); 4] = [
    // `pp = 7`, `a = 3`, three indices -- the instance the mutations are
    // refuted at.
    (6, 3, 3),
    // `pp = 5`, `a = 2`.
    (4, 2, 2),
    // `pp = 4`: EVEN and COMPOSITE.
    (3, 3, 3),
    // `pp = 3`, `a = 3`: `gcd 3 3 = 3`, so NOT coprime.
    (2, 3, 1),
];

impl Fixture {
    fn new() -> Self {
        let mut k = Kernel::new();
        let p = build_nat_prelude(&mut k).expect("Nat prelude must build");
        let st = NatState::new(&mut k, p);
        Self { k, p, st }
    }

    /// `fun j => leastResidue (succ ap) a (succ j)`.
    fn residue_fn(&mut self, ap: u32, a: u32) -> ExprId {
        let p = self.p;
        self.shifted(ap, a, p.least_residue)
    }

    /// `fun j => gaussFold (succ ap) a (succ j)`.
    fn fold_fn(&mut self, ap: u32, a: u32) -> ExprId {
        let p = self.p;
        self.shifted(ap, a, p.gauss_fold)
    }

    /// `fun j => gaussSignNeg (succ ap) a (succ j)`.
    fn sign_fn(&mut self, ap: u32, a: u32) -> ExprId {
        let p = self.p;
        self.shifted(ap, a, p.gauss_sign_neg)
    }

    fn shifted(&mut self, ap: u32, a: u32, name: crate::name::NameId) -> ExprId {
        let nat = self.nat_ty();
        let ap_e = self.num(ap);
        let pp = self.succ(ap_e);
        let a_e = self.num(a);
        let j_fv = self.fresh_fvar();
        let j = self.k.fvar(j_fv);
        let sj = self.succ(j);
        let body = self.const_app(name, &[pp, a_e, sj]);
        self.lam_fv(j_fv, nat, body)
    }

    /// `sumRangeIf sign fold m` at concrete arguments.
    fn conditional_fold_sum(&mut self, ap: u32, a: u32, m: u32) -> ExprId {
        let p = self.p;
        let sign = self.sign_fn(ap, a);
        let fold = self.fold_fn(ap, a);
        let m_e = self.num(m);
        self.const_app(p.sum_range_if, &[sign, fold, m_e])
    }

    fn reduces_to(&mut self, term: ExprId, value: u32) -> bool {
        let v = self.num(value);
        self.k.def_eq(term, v)
    }
}

/// The arithmetic the theorem asserts, checked in Rust before any proof term
/// is built — and checked to be non-degenerate: at every instance used the
/// negative count and the negative fold sum matter, except the deliberately
/// trivial non-coprime one, which is called out here rather than hidden.
#[test]
fn the_identity_holds_numerically_at_every_instance() {
    for (ap, a, m) in INSTANCES {
        let pp = ap + 1;
        let s = sums(pp, a, m);
        assert_eq!(
            s.residues + (s.negative_folds + s.negative_folds),
            s.folds + pp * s.count,
            "the identity must hold at (pp,a,m) = ({pp},{a},{m})"
        );
        assert_eq!(
            s.negative_folds + s.positive_folds,
            s.folds,
            "the two conditional halves must partition the fold sum"
        );
    }

    // The first three instances are non-degenerate: the negative count is
    // nonzero, so `pp * count` is really carrying weight.
    for (ap, a, m) in [INSTANCES[0], INSTANCES[1], INSTANCES[2]] {
        let s = sums(ap + 1, a, m);
        assert!(s.count > 0, "instance ({ap},{a},{m}) must have a negative");
        assert!(s.negative_folds > 0);
    }
    // The fourth is degenerate (every aggregate is zero) and is here only to
    // show that a NON-COPRIME pair is admitted at all.
    let degenerate = sums(3, 3, 1);
    assert_eq!(
        (
            degenerate.residues,
            degenerate.folds,
            degenerate.count,
            degenerate.negative_folds
        ),
        (0, 0, 0, 0)
    );
}

/// **The three wrong readings are FALSE**, at `(pp, a, m) = (7, 3, 3)`.
/// Each would type-check; none is refuted by the well-typedness of the
/// statement, which is why they are refuted by numbers here.
#[test]
fn the_wrong_readings_are_false_at_a_named_witness() {
    let (pp, a, m) = (7u32, 3u32, 3u32);
    let s = sums(pp, a, m);
    assert_eq!(
        (s.residues, s.folds, s.count, s.negative_folds),
        (11, 6, 1, 1)
    );

    // The identity itself.
    assert_eq!(s.residues + (s.negative_folds + s.negative_folds), 13);
    assert_eq!(s.folds + pp * s.count, 13);

    // M1: the doubling dropped -- `Σ residue = Σ fold + pp·N`.
    assert_ne!(s.residues, s.folds + pp * s.count, "11 vs 13");

    // M2: the COMPLEMENT's fold sum doubled instead of the selected one.
    assert_ne!(
        s.residues + (s.positive_folds + s.positive_folds),
        s.folds + pp * s.count,
        "21 vs 13"
    );

    // M3: the conditional sum taken over the RESIDUES rather than the folds.
    assert_ne!(
        s.residues + (s.negative_residues + s.negative_residues),
        s.folds + pp * s.count,
        "23 vs 13"
    );
}

/// `Nat.leastResidue_sumRange_reconcile` applies at all four instances, and
/// every aggregate in the statement reduces to the number Rust computed.
#[test]
fn the_reconciliation_applies_and_every_aggregate_computes() {
    let mut f = Fixture::new();
    let p = f.p;

    for (ap, a, m) in INSTANCES {
        let pp = ap + 1;
        let s = sums(pp, a, m);

        let ap_e = f.num(ap);
        let a_e = f.num(a);
        let m_e = f.num(m);
        let instance = f.lemma(p.least_residue_sum_range_reconcile, &[ap_e, a_e, m_e]);
        let inferred =
            f.k.infer(instance)
                .expect("the concrete instance must type-check");

        // The statement, rebuilt here independently of the declaration.
        let resid_fn = f.residue_fn(ap, a);
        let fold_fn = f.fold_fn(ap, a);
        let m_e2 = f.num(m);
        let sum_resid = f.sum_range(resid_fn, m_e2);
        let m_e3 = f.num(m);
        let sum_fold = f.sum_range(fold_fn, m_e3);
        let sif = f.conditional_fold_sum(ap, a, m);
        let doubled = f.add(sif, sif);
        let lhs = f.add(sum_resid, doubled);
        let pp_e = {
            let ap2 = f.num(ap);
            f.succ(ap2)
        };
        let m_e4 = f.num(m);
        let count = f.const_app(p.gauss_neg_count, &[pp_e, a_e, m_e4]);
        let scaled = f.mul(pp_e, count);
        let rhs = f.add(sum_fold, scaled);
        let expected = f.eq(lhs, rhs);
        assert!(
            f.k.def_eq(inferred, expected),
            "at (pp,a,m) = ({pp},{a},{m}) the conclusion is not the reconciliation"
        );

        // Every aggregate reduces -- so this is not two stuck sums agreeing.
        assert!(
            f.reduces_to(sum_resid, s.residues),
            "Σ leastResidue must be {} at (pp,a,m) = ({pp},{a},{m})",
            s.residues
        );
        assert!(
            f.reduces_to(sum_fold, s.folds),
            "Σ gaussFold must be {}",
            s.folds
        );
        assert!(
            f.reduces_to(sif, s.negative_folds),
            "the conditional fold sum must be {}",
            s.negative_folds
        );
        assert!(
            f.reduces_to(count, s.count),
            "gaussNegCount must be {}",
            s.count
        );
        // Negative control on those four `def_eq`s at the one instance where
        // every value is nonzero: each rejects its own neighbour.
        if s.count > 0 {
            assert!(!f.reduces_to(sum_resid, s.residues + 1));
            assert!(!f.reduces_to(sum_fold, s.folds + 1));
            assert!(!f.reduces_to(sif, s.negative_folds + 1));
            assert!(!f.reduces_to(count, s.count + 1));
        }

        // And both sides of the identity reduce to the same number.
        let total = s.residues + s.negative_folds + s.negative_folds;
        assert!(f.reduces_to(lhs, total), "the left side must be {total}");
        assert!(f.reduces_to(rhs, total), "the right side must be {total}");
    }
}

/// **The doubling is load-bearing in the kernel, not just in Rust.** At
/// `(pp,a,m) = (7,3,3)` the undoubled left side reduces to `11` and the
/// right side to `13`, so the statement with the doubling dropped is FALSE
/// at an instance the theorem's (empty) hypotheses reach.
#[test]
fn dropping_the_doubling_gives_a_false_identity() {
    let mut f = Fixture::new();
    let p = f.p;
    let (ap, a, m) = (6u32, 3u32, 3u32);

    let resid_fn = f.residue_fn(ap, a);
    let m_e = f.num(m);
    let sum_resid = f.sum_range(resid_fn, m_e);
    let fold_fn = f.fold_fn(ap, a);
    let m_e2 = f.num(m);
    let sum_fold = f.sum_range(fold_fn, m_e2);
    let pp_e = {
        let ap_e = f.num(ap);
        f.succ(ap_e)
    };
    let a_e = f.num(a);
    let m_e3 = f.num(m);
    let count = f.const_app(p.gauss_neg_count, &[pp_e, a_e, m_e3]);
    let scaled = f.mul(pp_e, count);
    let rhs = f.add(sum_fold, scaled);

    assert!(f.reduces_to(sum_resid, 11));
    assert!(f.reduces_to(rhs, 13));
    assert!(
        !f.k.def_eq(sum_resid, rhs),
        "without the doubling the identity is FALSE"
    );
}

/// The declaration rests on zero axioms.
#[test]
fn the_reconciliation_rests_on_no_axiom() {
    let f = Fixture::new();
    let p = f.p;
    assert!(
        f.k.axiom_footprint(p.least_residue_sum_range_reconcile)
            .is_empty(),
        "{} must rest on zero axioms",
        f.k.display_name(p.least_residue_sum_range_reconcile)
    );
}

/// The declared type, pinned character for character.
///
/// Four distinctions the numeric instances above CANNOT see, and which this
/// pin is the only guard for:
///
/// - the conditional sum's predicate is `gaussSignNeg`, its summand
///   `gaussFold`, and its bound the same `m`;
/// - the modulus is `succ ap` in every one of its five occurrences;
/// - the doubled term sits on the LEFT of the equation, with the `pp·N` term
///   on the right (moving both would give a different, also-true, statement
///   no consumer could chain through);
/// - there is no hypothesis at all.
#[test]
fn the_reconciliation_states_the_intended_type() {
    use crate::env::Declaration;
    let mut k = Kernel::new();
    let p = build_nat_prelude(&mut k).expect("Nat prelude must build");

    let ty = match k
        .environment()
        .get(p.least_residue_sum_range_reconcile)
        .expect("the theorem must be declared")
    {
        Declaration::Theorem { ty, .. } => {
            let ty = *ty;
            k.render_lean(ty)
        }
        other => panic!("{other:?} is not a theorem"),
    };
    assert_eq!(ty, EXPECTED, "the reconciliation states a different type");

    // It really is hypothesis-free: three `AxNat` binders and nothing else
    // before the `Eq`. The negative control is that the same query finds a
    // hypothesis in `gauss_fold_sumRange_eq`, which HAS one.
    assert!(
        !ty.contains("AxNat.gcd"),
        "the reconciliation must not mention `gcd`"
    );
    let coprime_ty = match k
        .environment()
        .get(p.gauss_fold_sum_range_eq)
        .expect("the sibling theorem must be declared")
    {
        Declaration::Theorem { ty, .. } => {
            let ty = *ty;
            k.render_lean(ty)
        }
        other => panic!("{other:?} is not a theorem"),
    };
    assert!(
        coprime_ty.contains("AxNat.gcd"),
        "positive control: `gauss_fold_sumRange_eq` DOES carry a coprimality hypothesis"
    );
}

const EXPECTED: &str = "((x0 : AxNat) -> ((x1 : AxNat) -> ((x2 : AxNat) -> Eq.{1} AxNat (AxNat.add (AxNat.sumRange (fun (x3 : AxNat) => AxNat.leastResidue (AxNat.succ x0) x1 (AxNat.succ x3)) x2) (AxNat.add (AxNat.sumRangeIf (fun (x3 : AxNat) => AxNat.gaussSignNeg (AxNat.succ x0) x1 (AxNat.succ x3)) (fun (x3 : AxNat) => AxNat.gaussFold (AxNat.succ x0) x1 (AxNat.succ x3)) x2) (AxNat.sumRangeIf (fun (x3 : AxNat) => AxNat.gaussSignNeg (AxNat.succ x0) x1 (AxNat.succ x3)) (fun (x3 : AxNat) => AxNat.gaussFold (AxNat.succ x0) x1 (AxNat.succ x3)) x2))) (AxNat.add (AxNat.sumRange (fun (x3 : AxNat) => AxNat.gaussFold (AxNat.succ x0) x1 (AxNat.succ x3)) x2) (AxNat.mul (AxNat.succ x0) (AxNat.gaussNegCount (AxNat.succ x0) x1 x2))))))";
