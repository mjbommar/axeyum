//! Discriminating checks for `nat_prelude::primrec`'s two constructions.
//!
//! # Why this file is shaped differently from every other `*_tests.rs` here
//!
//! Every other definition in this prelude is pinned by an EVALUATION test:
//! reduce it at concrete numerals and compare against a hand-computed table,
//! because `Kernel::add_declaration` type-checks a `Definition` and does not
//! evaluate it. `Nat.casesOn` gets exactly that treatment below.
//!
//! **`Nat.Primrec` is an inductive `Prop` and admits no such test.** There is
//! no value to reduce. A constructor stating a transposed, weakened or simply
//! wrong closure property type-checks as happily as the intended one, and
//! `axiom_footprint`, the prelude build and the environment-derived coverage
//! assertion are all blind to it. Declaring an inductive `Prop` means giving
//! up the safeguard the rest of this prelude leans on hardest, so this file
//! says what replaces it rather than leaving the gap unremarked.
//!
//! Three things replace it, and they fail on disjoint defect classes:
//!
//! 1. **The predicate does not evaluate, but its INDICES do.** Each
//!    constructor concludes at `Nat.Primrec <a concrete `Nat → Nat` term>`,
//!    and that term is an ordinary function this kernel reduces. So the
//!    evaluation test is recovered one level in: `def_eq` the constructor's
//!    INFERRED type against `Nat.Primrec F` for an `F` built here, and
//!    separately reduce `F` at numerals against a hand table. Two links, and
//!    together they pin the admitted index to a function checked by
//!    evaluation — a swapped `left`/`right`, or a `zero` returning its
//!    argument, breaks one link or the other.
//! 2. **Closed derivations, assembled from the real constructors and
//!    inferred.** A constructor whose hypothesis and conclusion shapes do not
//!    COMPOSE cannot appear in a derivation at all, and no per-constructor
//!    check sees that: mutually-consistent errors type-check individually and
//!    fail only when chained. Each derivation's conclusion is then evaluated,
//!    so it is not merely "the kernel accepted something".
//! 3. **A binder-count assertion per constructor**, so a constructor that
//!    silently lost a hypothesis states a WEAKER proposition and fails, rather
//!    than passing as a well-typed different theorem.
//!
//! # The hand-computed tables
//!
//! `Nat.pair a b := if a < b then b*b+a else a*a+a+b` (`avg_pair.rs`), and
//! `unpairLeft`/`unpairRight` are its components (`unpair.rs`, own table).
//!
//! For `prec` instantiated at `f := fun _ => 0` and `g := fun n => n+1`, the
//! index is `unpaired (fun z n => Nat.rec 0 (fun y IH => g (pair z (pair y
//! IH))) n)`. Simulated before any of this was written:
//!
//! | m | z = uL m | n = uR m | value | value if the two `pair`s are TRANSPOSED |
//! |---|----------|----------|-------|------------------------------------------|
//! | 0 | 0        | 0        | 0     | 0   (base case, discriminates nothing)   |
//! | 1 | 0        | 1        | 1     | 1   (coincides, discriminates nothing)   |
//! | 3 | 1        | 1        | **3** | **2**                                    |
//! | 4 | 0        | 2        | **10**| **13**                                   |
//!
//! `m = 3` and `m = 4` are the discriminating arguments and `m = 0`/`m = 1`
//! are deliberately NOT used as controls — they agree under the transposition,
//! so a control built on them would pass while measuring nothing. `m = 5`
//! reaches 102, which is a 102-deep unary tower in this prelude, and is
//! avoided for that reason alone.

use crate::{ExprNode, Kernel, NatOps, NatPrelude, NatState, build_nat_prelude};
use crate::expr::ExprId;

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

impl Fixture {
    fn new() -> Self {
        let mut k = Kernel::new();
        let p = build_nat_prelude(&mut k).expect("Nat prelude must build");
        let st = NatState::new(&mut k, p);
        Self { k, p, st }
    }

    /// The type the kernel actually admitted for a constructor.
    fn ctor_ty(&mut self, name: crate::NameId) -> ExprId {
        let c = self.k.const_(name, vec![]);
        self.k.infer(c).expect("constructor must infer")
    }

    /// `Nat.Primrec f`, rebuilt here rather than imported from the
    /// declaration site.
    fn primrec_at(&mut self, f: ExprId) -> ExprId {
        let p = self.p;
        self.const_app(p.primrec, &[f])
    }

    /// How many Pi binders a type has before its head. A constructor that
    /// lost a hypothesis has fewer.
    fn pi_arity(&self, mut ty: ExprId) -> usize {
        let mut n = 0;
        while let ExprNode::Pi(_, _, body, _) = *self.k.expr_node(ty) {
            n += 1;
            ty = body;
        }
        n
    }
}

/// `Nat.casesOn` reduces to the right branch at concrete numerals, with a
/// negative control for the branches SWAPPED.
///
/// This is the ordinary evaluation test, and `casesOn` gets one because it is
/// a `Definition` — the argument ORDER (scrutinee first, then the zero and
/// succ minors) is exactly the sort of thing the type cannot see, since a
/// `casesOn` that consulted the wrong branch is equally well-typed.
///
/// `casesOn 0 7 (fun n => n)` must be `7` and `casesOn 5 7 (fun n => n)` must
/// be `4` — the PREDECESSOR, not `5`, which is what makes this a check of the
/// `motive n.succ` binder rather than of the scrutinee passing through.
#[test]
fn cases_on_selects_the_right_branch_and_exposes_the_predecessor() {
    let mut f = Fixture::new();
    let p = f.p;
    let nat = f.nat_ty();
    let one = f.level_one();

    let num: Vec<_> = (0u32..=8).map(|i| f.num(i)).collect();
    let anon = f.anon_name();
    // motive := fun _ => Nat, so `casesOn` eliminates into `Nat`.
    let motive = f.k.lam(anon, nat, nat, crate::BinderInfo::Default);
    // succ minor := fun n => n, which RETURNS THE PREDECESSOR.
    let pred_minor = {
        let n_fv = f.fresh_fvar();
        let n = f.k.fvar(n_fv);
        f.lam_fv(n_fv, nat, n)
    };
    let cases_on = f.k.const_(p.cases_on, vec![one]);

    // zero branch: `casesOn 0 7 pred = 7`.
    let at_zero = f.apply(cases_on, &[motive, num[0], num[7], pred_minor]);
    assert!(
        f.k.def_eq(at_zero, num[7]),
        "casesOn 0 7 (fun n => n) must take the ZERO branch and give 7"
    );

    // succ branch: `casesOn 5 7 pred = 4`.
    let at_five = f.apply(cases_on, &[motive, num[5], num[7], pred_minor]);
    assert!(
        f.k.def_eq(at_five, num[4]),
        "casesOn 5 7 (fun n => n) must take the SUCC branch and give the \
         predecessor 4"
    );

    // Negative control 1 -- the branches are not swapped. A `casesOn` that
    // consulted the zero minor on a successor would give 7 here.
    assert!(
        !f.k.def_eq(at_five, num[7]),
        "negative control: casesOn 5 7 pred must NOT be 7 (branches swapped)"
    );
    // Negative control 2 -- the succ minor receives the PREDECESSOR, not the
    // scrutinee. A `casesOn` built as `Nat.rec z (fun n _ => s (succ n))`
    // would give 5.
    assert!(
        !f.k.def_eq(at_five, num[5]),
        "negative control: casesOn 5 7 pred must NOT be 5 (succ minor was \
         handed the scrutinee rather than its predecessor)"
    );
}

/// Every `Nat.Primrec` constructor's ADMITTED index is the function this
/// module claims it is, checked by reducing that function at numerals.
///
/// The substitute for an evaluation test on an inductive `Prop`, described in
/// this file's header. For each constructor: `def_eq` its inferred type
/// against `Nat.Primrec F` for an `F` built here, then reduce `F` at concrete
/// arguments against a hand table. Neither link alone is worth much; together
/// they say the kernel admitted a closure property about a function whose
/// values are known.
#[test]
fn primrec_constructor_indices_are_the_intended_functions() {
    let mut f = Fixture::new();
    let p = f.p;
    let nat = f.nat_ty();
    let num: Vec<_> = (0u32..=8).map(|i| f.num(i)).collect();

    // --- zero : Primrec (fun _ => 0) ------------------------------------
    let zero_idx = {
        let anon = f.anon_name();
        let z = f.zero();
        f.k.lam(anon, nat, z, crate::BinderInfo::Default)
    };
    let zero_ty = f.ctor_ty(p.primrec_zero);
    let expect = f.primrec_at(zero_idx);
    assert!(
        f.k.def_eq(zero_ty, expect),
        "Nat.Primrec.zero must conclude at the constant-zero function"
    );
    // and that function is constantly zero, not the identity.
    let applied = f.apply(zero_idx, &[num[5]]);
    assert!(f.k.def_eq(applied, num[0]), "the zero index at 5 must be 0");
    assert!(
        !f.k.def_eq(applied, num[5]),
        "negative control: the zero index must NOT be the identity"
    );

    // --- succ : Primrec Nat.succ ----------------------------------------
    let succ_idx = {
        let n_fv = f.fresh_fvar();
        let n = f.k.fvar(n_fv);
        let sn = f.succ(n);
        f.lam_fv(n_fv, nat, sn)
    };
    let succ_ty = f.ctor_ty(p.primrec_succ);
    let expect = f.primrec_at(succ_idx);
    assert!(
        f.k.def_eq(succ_ty, expect),
        "Nat.Primrec.succ must conclude at the successor function"
    );
    let applied = f.apply(succ_idx, &[num[5]]);
    assert!(f.k.def_eq(applied, num[6]), "the succ index at 5 must be 6");

    // --- left : Primrec Nat.unpairLeft ----------------------------------
    //
    // `n = 5` is the discriminator: `unpairLeft 5 = 1` and
    // `unpairRight 5 = 2`, so a SWAP of the two constructors fails here.
    let left_idx = {
        let n_fv = f.fresh_fvar();
        let n = f.k.fvar(n_fv);
        let body = f.const_app(p.unpair_left, &[n]);
        f.lam_fv(n_fv, nat, body)
    };
    let left_ty = f.ctor_ty(p.primrec_left);
    let expect = f.primrec_at(left_idx);
    assert!(
        f.k.def_eq(left_ty, expect),
        "Nat.Primrec.left must conclude at Nat.unpairLeft"
    );
    let applied = f.apply(left_idx, &[num[5]]);
    assert!(f.k.def_eq(applied, num[1]), "the left index at 5 must be 1");
    assert!(
        !f.k.def_eq(applied, num[2]),
        "negative control: the left index at 5 must NOT be 2 (left/right \
         swapped)"
    );

    // --- right : Primrec Nat.unpairRight --------------------------------
    let right_idx = {
        let n_fv = f.fresh_fvar();
        let n = f.k.fvar(n_fv);
        let body = f.const_app(p.unpair_right, &[n]);
        f.lam_fv(n_fv, nat, body)
    };
    let right_ty = f.ctor_ty(p.primrec_right);
    let expect = f.primrec_at(right_idx);
    assert!(
        f.k.def_eq(right_ty, expect),
        "Nat.Primrec.right must conclude at Nat.unpairRight"
    );
    let applied = f.apply(right_idx, &[num[5]]);
    assert!(f.k.def_eq(applied, num[2]), "the right index at 5 must be 2");
    assert!(
        !f.k.def_eq(applied, num[1]),
        "negative control: the right index at 5 must NOT be 1 (left/right \
         swapped)"
    );

    // The two nullary function constructors are DIFFERENT propositions --
    // this is the assertion that a copy-paste between them fails.
    assert!(
        !f.k.def_eq(left_ty, right_ty),
        "negative control: Nat.Primrec.left and .right must state different \
         propositions"
    );
    assert!(
        !f.k.def_eq(zero_ty, succ_ty),
        "negative control: Nat.Primrec.zero and .succ must state different \
         propositions"
    );
}

/// Each `Nat.Primrec` constructor binds the number of arguments Mathlib's
/// does, so one that silently lost a hypothesis fails here rather than
/// passing as a well-typed WEAKER statement.
///
/// Mathlib's shapes: `zero`/`succ`/`left`/`right` are closed (0 binders);
/// `pair`/`comp`/`prec` each take `{f g}` plus two `Primrec` premises, so 4.
/// A `pair` written with one premise would still type-check and would state
/// something strictly weaker; nothing else in this file would notice.
#[test]
fn primrec_constructors_bind_the_arguments_mathlib_binds() {
    let mut f = Fixture::new();
    let p = f.p;

    for (name, expected, label) in [
        (p.primrec_zero, 0usize, "zero"),
        (p.primrec_succ, 0, "succ"),
        (p.primrec_left, 0, "left"),
        (p.primrec_right, 0, "right"),
        (p.primrec_pair, 4, "pair"),
        (p.primrec_comp, 4, "comp"),
        (p.primrec_prec, 4, "prec"),
    ] {
        let ty = f.ctor_ty(name);
        let arity = f.pi_arity(ty);
        assert_eq!(
            arity, expected,
            "Nat.Primrec.{label} must bind {expected} arguments ({{f g}} plus \
             two Primrec premises for the three closure constructors), got \
             {arity}"
        );
    }
}

/// Closed derivations built from the real constructors type-check, AND the
/// functions they conclude about evaluate correctly.
///
/// This is the check no per-constructor assertion can make. A set of
/// constructors can each be individually well-typed against an expectation
/// that is wrong in the same way, and only chaining them through an actual
/// application exposes it — the mutually-consistent-errors failure. Building
/// `comp succ succ` requires `comp`'s premise shape to match what `succ`
/// concludes, and `prec zero succ` requires the same of `prec`.
///
/// Each derivation's conclusion is then reduced at numerals, so this test
/// cannot pass merely because the kernel accepted some term.
#[test]
fn primrec_closed_derivations_compose_and_their_functions_evaluate() {
    let mut f = Fixture::new();
    let p = f.p;
    let nat = f.nat_ty();
    let num: Vec<_> = (0u32..=13).map(|i| f.num(i)).collect();

    let zero_pf = f.k.const_(p.primrec_zero, vec![]);
    let succ_pf = f.k.const_(p.primrec_succ, vec![]);

    let zero_idx = {
        let anon = f.anon_name();
        let z = f.zero();
        f.k.lam(anon, nat, z, crate::BinderInfo::Default)
    };
    let succ_idx = {
        let n_fv = f.fresh_fvar();
        let n = f.k.fvar(n_fv);
        let sn = f.succ(n);
        f.lam_fv(n_fv, nat, sn)
    };

    // --- comp succ succ : Primrec (fun n => n + 2) ----------------------
    let comp_term = f.const_app(p.primrec_comp, &[succ_idx, succ_idx, succ_pf, succ_pf]);
    let comp_ty = f
        .k
        .infer(comp_term)
        .expect("comp succ succ must type-check: its premise shape must match \
                 what succ concludes");
    let doubled = {
        let n_fv = f.fresh_fvar();
        let n = f.k.fvar(n_fv);
        let s1 = f.succ(n);
        let s2 = f.succ(s1);
        f.lam_fv(n_fv, nat, s2)
    };
    let expect = f.primrec_at(doubled);
    assert!(
        f.k.def_eq(comp_ty, expect),
        "comp succ succ must conclude at the twice-successor function"
    );
    let applied = f.apply(doubled, &[num[3]]);
    assert!(
        f.k.def_eq(applied, num[5]),
        "the composed function at 3 must be 5"
    );

    // --- prec zero succ -------------------------------------------------
    //
    // The index is `unpaired (fun z n => Nat.rec 0 (fun y IH =>
    // succ (pair z (pair y IH))) n)`. Values from this file's header table.
    let prec_term = f.const_app(p.primrec_prec, &[zero_idx, succ_idx, zero_pf, succ_pf]);
    let prec_ty = f
        .k
        .infer(prec_term)
        .expect("prec zero succ must type-check");

    // Rebuild the index here, so the reduction below is against a term this
    // test owns, and tie it to the admitted one by def_eq.
    let prec_idx = {
        let z_fv = f.fresh_fvar();
        let z = f.k.fvar(z_fv);
        let n_fv = f.fresh_fvar();
        let n = f.k.fvar(n_fv);
        let anon = f.anon_name();
        let motive = f.k.lam(anon, nat, nat, crate::BinderInfo::Default);
        let base = f.zero();
        let step = {
            let y_fv = f.fresh_fvar();
            let y = f.k.fvar(y_fv);
            let ih_fv = f.fresh_fvar();
            let ih = f.k.fvar(ih_fv);
            let inner = f.const_app(p.pair_fn, &[y, ih]);
            let outer = f.const_app(p.pair_fn, &[z, inner]);
            let body = f.succ(outer);
            let with_ih = f.lam_fv(ih_fv, nat, body);
            f.lam_fv(y_fv, nat, with_ih)
        };
        let one = f.level_one();
        let rec = f.k.const_(p.rec, vec![one]);
        let rec_body = f.apply(rec, &[motive, base, step, n]);
        let with_n = f.lam_fv(n_fv, nat, rec_body);
        let binary = f.lam_fv(z_fv, nat, with_n);
        f.const_app(p.unpaired, &[binary])
    };
    let expect = f.primrec_at(prec_idx);
    assert!(
        f.k.def_eq(prec_ty, expect),
        "prec zero succ must conclude at the unpaired primitive recursion"
    );

    // m = 3 and m = 4 are the arguments that DISCRIMINATE the nesting
    // `pair z (pair y IH)` from the transposed `pair (pair y IH) z`; m = 0
    // and m = 1 agree under the transposition and are deliberately not used
    // as controls. Simulated before this test was written.
    for (m, expected) in [(0usize, 0usize), (3, 3), (4, 10)] {
        let applied = f.apply(prec_idx, &[num[m]]);
        assert!(
            f.k.def_eq(applied, num[expected]),
            "the prec index at {m} must be {expected}"
        );
    }

    // Negative controls -- the transposed nesting gives 2 at m = 3 and 13 at
    // m = 4. Both are asserted so that a transposition failing to change one
    // value cannot pass unnoticed.
    let at_three = f.apply(prec_idx, &[num[3]]);
    assert!(
        !f.k.def_eq(at_three, num[2]),
        "negative control: the prec index at 3 must NOT be 2 (the two \
         Nat.pair applications are transposed)"
    );
    let at_four = f.apply(prec_idx, &[num[4]]);
    assert!(
        !f.k.def_eq(at_four, num[13]),
        "negative control: the prec index at 4 must NOT be 13 (the two \
         Nat.pair applications are transposed)"
    );
}
