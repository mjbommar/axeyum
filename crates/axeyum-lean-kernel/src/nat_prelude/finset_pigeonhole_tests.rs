//! Concrete-instance tests for the pigeonhole family (ADR-1593):
//! `Nat.countRange_le_of_injOn`, `Nat.Finset.lt_bound_of_memB`,
//! `Nat.Finset.card_le_of_injOn`, `Nat.Finset.pigeonhole`,
//! `Nat.Finset.allBelow_false_witness` and `Nat.Finset.exists_collision`.
//!
//! A separate file rather than an addition to `finset_tests.rs`, per this
//! development's merge-hazard note.
//!
//! Nothing here introduces a new `Definition`, so the usual "the kernel cannot
//! tell a `Definition` is wrong" hazard does not apply directly — but the same
//! hazard applies to a THEOREM whose statement is not what its name says, and
//! that is what these checks are for. A `card_le_of_injOn` with its two `card`s
//! transposed, an `exists_collision` whose pair need not be DISTINCT, a
//! `pigeonhole` whose strict inequality points the other way: every one of
//! those would be admitted by the trusted gate, carry an empty axiom footprint,
//! and pass every sweep in this repository. Only a concrete instance whose
//! numerals are hand-computed, or a whole declared type rebuilt independently,
//! separates them.
//!
//! Each positive is paired with the specific wrong statement it rules out, and
//! two of the negative controls are the sharper kind: a hypothesis that cannot
//! be DISCHARGED (`infer` must fail), not merely a conclusion that happens to
//! be false.
//!
//! Magnitudes are tiny on purpose — this prelude's numerals are unary `succ`
//! towers. The largest bound any fold below runs over is `8`.

use crate::expr::ExprId;
use crate::tc::{LocalContext, LocalDecl};
use crate::{BinderInfo, Kernel, NatOps, NatPrelude, NatState, build_nat_prelude};

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

    fn singleton(&mut self, a: u32) -> ExprId {
        let lit = self.num(a);
        let name = self.p.finset_singleton;
        self.const_app(name, &[lit])
    }

    fn range(&mut self, n: u32) -> ExprId {
        let lit = self.num(n);
        let name = self.p.finset_range;
        self.const_app(name, &[lit])
    }

    fn union(&mut self, s: ExprId, t: ExprId) -> ExprId {
        let name = self.p.finset_union;
        self.const_app(name, &[s, t])
    }

    /// `{a, b}` as `singleton a ∪ singleton b`.
    fn pair_set(&mut self, a: u32, b: u32) -> ExprId {
        let sa = self.singleton(a);
        let sb = self.singleton(b);
        self.union(sa, sb)
    }

    fn card(&mut self, s: ExprId) -> ExprId {
        let name = self.p.finset_card;
        self.const_app(name, &[s])
    }

    fn memb_at(&mut self, s: ExprId, i: ExprId) -> ExprId {
        let name = self.p.finset_mem_b;
        self.const_app(name, &[s, i])
    }

    /// `fun _ : Nat => c`.
    fn constant_map(&mut self, c: u32) -> ExprId {
        let nat = self.nat_ty();
        let k_fv = self.fresh_fvar();
        let lit = self.num(c);
        self.lam_fv(k_fv, nat, lit)
    }

    /// `fun k : Nat => k`.
    fn identity_map(&mut self) -> ExprId {
        let nat = self.nat_ty();
        let k_fv = self.fresh_fvar();
        let k = self.k.fvar(k_fv);
        self.lam_fv(k_fv, nat, k)
    }

    /// `fun k : Nat => Nat.ble c k` — the predicate `c ≤ ·`.
    fn at_least(&mut self, c: u32) -> ExprId {
        let nat = self.nat_ty();
        let lit = self.num(c);
        let k_fv = self.fresh_fvar();
        let k = self.k.fvar(k_fv);
        let body = self.ble(lit, k);
        self.lam_fv(k_fv, nat, body)
    }

    /// `fun _ : Nat => Bool.true`.
    fn always_true(&mut self) -> ExprId {
        let nat = self.nat_ty();
        let bool_true = self.bool_true();
        let k_fv = self.fresh_fvar();
        self.lam_fv(k_fv, nat, bool_true)
    }

    /// `∀ i j, memB s i = true → memB s j = true → g i = g j → i = j`.
    fn inj_on_members(&mut self, s: ExprId, g: ExprId) -> ExprId {
        let nat = self.nat_ty();
        let true_ = self.bool_true();
        let i_fv = self.fresh_fvar();
        let i = self.k.fvar(i_fv);
        let j_fv = self.fresh_fvar();
        let j = self.k.fvar(j_fv);

        let gi = self.apply(g, &[i]);
        let gj = self.apply(g, &[j]);
        let concl = self.eq(i, j);
        let hyp_eq = self.eq(gi, gj);
        let s3 = self.arrow(hyp_eq, concl);
        let mj = self.memb_at(s, j);
        let sel_j = self.bool_eq(mj, true_);
        let s2 = self.arrow(sel_j, s3);
        let mi = self.memb_at(s, i);
        let sel_i = self.bool_eq(mi, true_);
        let s1 = self.arrow(sel_i, s2);
        let with_j = self.pi_fv(j_fv, nat, s1);
        self.pi_fv(i_fv, nat, with_j)
    }

    /// `∀ i, memB s i = true → memB t (g i) = true`.
    fn maps_members(&mut self, s: ExprId, t: ExprId, g: ExprId) -> ExprId {
        let nat = self.nat_ty();
        let true_ = self.bool_true();
        let i_fv = self.fresh_fvar();
        let i = self.k.fvar(i_fv);
        let gi = self.apply(g, &[i]);
        let t_gi = self.memb_at(t, gi);
        let concl = self.bool_eq(t_gi, true_);
        let mi = self.memb_at(s, i);
        let sel_i = self.bool_eq(mi, true_);
        let inner = self.arrow(sel_i, concl);
        self.pi_fv(i_fv, nat, inner)
    }

    /// `Exists.{1} Nat pred`.
    fn exists_nat(&mut self, pred: ExprId) -> ExprId {
        let one = self.level_one();
        let nat = self.nat_ty();
        let name = self.p.logic.exists_;
        let ex = self.k.const_(name, vec![one]);
        self.apply(ex, &[nat, pred])
    }

    fn and_of(&mut self, left: ExprId, right: ExprId) -> ExprId {
        let name = self.p.logic.and;
        self.const_app(name, &[left, right])
    }

    /// Open a local context holding one free variable per supplied type.
    fn open(&mut self, tys: &[ExprId]) -> (Vec<ExprId>, LocalContext) {
        let anon = self.anon_name();
        let mut ctx = LocalContext::new();
        let mut vars = Vec::with_capacity(tys.len());
        for ty in tys {
            let fv = self.fresh_fvar();
            vars.push(self.k.fvar(fv));
            ctx.push(LocalDecl {
                fvar: fv,
                name: anon,
                ty: *ty,
                info: BinderInfo::Default,
            });
        }
        (vars, ctx)
    }
}

/// EVERY declaration under `Nat.Finset` is axiom-free, with the population
/// read from the ENVIRONMENT rather than from a list written here.
///
/// `finset_tests.rs`'s sibling check enumerates a hand-written array, which
/// measures the maintainer's memory: a declaration added to `finset.rs` and
/// forgotten there is not checked by it and nothing goes red. This one asks the
/// kernel what exists. The five names ADR-1593 adds are then asserted to be
/// AMONG them, so the derivation cannot silently return an empty population and
/// pass — the failure mode a prefix filter has by construction.
#[test]
fn every_finset_declaration_in_the_environment_is_axiom_free() {
    let f = Fixture::new();

    let mut rendered: Vec<(String, crate::name::NameId)> = Vec::new();
    for (&name, _) in f.k.environment().iter() {
        let text = f.k.display_name(name).to_string();
        if text == "Nat.Finset" || text.starts_with("Nat.Finset.") {
            rendered.push((text, name));
        }
    }
    rendered.sort_by(|a, b| a.0.cmp(&b.0));

    assert!(
        rendered.len() >= 33,
        "the environment must carry the whole Nat.Finset namespace, found {}: {:?}",
        rendered.len(),
        rendered.iter().map(|r| &r.0).collect::<Vec<_>>()
    );

    for (text, name) in &rendered {
        let footprint = f.k.axiom_footprint(*name);
        assert!(
            footprint.is_empty(),
            "{text} must be axiom-free, got {} names",
            footprint.len()
        );
    }

    let names: Vec<&str> = rendered.iter().map(|r| r.0.as_str()).collect();
    for required in [
        "Nat.Finset.lt_bound_of_memB",
        "Nat.Finset.card_le_of_injOn",
        "Nat.Finset.pigeonhole",
        "Nat.Finset.allBelow_false_witness",
        "Nat.Finset.exists_collision",
    ] {
        assert!(
            names.contains(&required),
            "{required} must be in the derived population, which held {names:?}"
        );
    }
}

/// `Nat.countRange_le_of_injOn`'s DECLARED TYPE is the two-hypothesis form —
/// no inverse `τ`, no round-trip equations — rebuilt here independently.
///
/// This is the whole difference from `Nat.countRange_bij`, and it is invisible
/// at a concrete instance: both laws are inhabited wherever a bijection exists.
/// An extra binder, a reordered one, or a conclusion stated as `Eq` rather than
/// `Le` fails this check rather than passing it.
#[test]
fn count_range_le_of_inj_on_takes_an_injection_and_nothing_else() {
    let mut f = Fixture::new();
    let p = f.p;
    let nat = f.nat_ty();

    let declared = {
        let c = f.k.const_(p.count_range_le_of_inj_on, vec![]);
        match f.k.infer(c) {
            Ok(t) => t,
            Err(e) => panic!("the constant must have a type: {}", f.explain(&e)),
        }
    };

    let rebuilt = {
        let bool_ty = f.bool_ty();
        let pred_ty = f.arrow(nat, bool_ty);
        let fn_ty = f.arrow(nat, nat);
        let true_ = f.bool_true();

        let pp_fv = f.fresh_fvar();
        let pp = f.k.fvar(pp_fv);
        let q_fv = f.fresh_fvar();
        let q = f.k.fvar(q_fv);
        let sg_fv = f.fresh_fvar();
        let sg = f.k.fvar(sg_fv);
        let n_fv = f.fresh_fvar();
        let n = f.k.fvar(n_fv);
        let m_fv = f.fresh_fvar();
        let m = f.k.fvar(m_fv);

        let h1 = {
            let i_fv = f.fresh_fvar();
            let i = f.k.fvar(i_fv);
            let j_fv = f.fresh_fvar();
            let j = f.k.fvar(j_fv);
            let si = f.apply(sg, &[i]);
            let sj = f.apply(sg, &[j]);
            let concl = f.eq(i, j);
            let heq = f.eq(si, sj);
            let s5 = f.arrow(heq, concl);
            let pj = f.apply(pp, &[j]);
            let sel_j = f.bool_eq(pj, true_);
            let s4 = f.arrow(sel_j, s5);
            let bj = f.lt(j, n);
            let s3 = f.arrow(bj, s4);
            let pi = f.apply(pp, &[i]);
            let sel_i = f.bool_eq(pi, true_);
            let s2 = f.arrow(sel_i, s3);
            let bi = f.lt(i, n);
            let s1 = f.arrow(bi, s2);
            let with_j = f.pi_fv(j_fv, nat, s1);
            f.pi_fv(i_fv, nat, with_j)
        };
        let h2 = {
            let i_fv = f.fresh_fvar();
            let i = f.k.fvar(i_fv);
            let si = f.apply(sg, &[i]);
            let bound = f.lt(si, m);
            let q_si = f.apply(q, &[si]);
            let selected = f.bool_eq(q_si, true_);
            let concl = f.and_of(bound, selected);
            let pi = f.apply(pp, &[i]);
            let sel_i = f.bool_eq(pi, true_);
            let s2 = f.arrow(sel_i, concl);
            let bi = f.lt(i, n);
            let s1 = f.arrow(bi, s2);
            f.pi_fv(i_fv, nat, s1)
        };

        let count = p.count_range;
        let lhs = f.const_app(count, &[pp, n]);
        let rhs = f.const_app(count, &[q, m]);
        let concl = f.le(lhs, rhs);
        let s2 = f.arrow(h2, concl);
        let s1 = f.arrow(h1, s2);
        let over_m = f.pi_fv(m_fv, nat, s1);
        let over_n = f.pi_fv(n_fv, nat, over_m);
        let over_sg = f.pi_fv(sg_fv, fn_ty, over_n);
        let over_q = f.pi_fv(q_fv, pred_ty, over_sg);
        f.pi_fv(pp_fv, pred_ty, over_q)
    };

    assert!(
        f.k.def_eq(declared, rebuilt),
        "the declared type must be the TWO-hypothesis injection form written \
         out here -- an inverse, a round trip, or an Eq conclusion would fail"
    );
    assert!(
        f.k.axiom_footprint(p.count_range_le_of_inj_on).is_empty(),
        "countRange_le_of_injOn must rest on zero axioms"
    );
}

/// `Nat.Finset.lt_bound_of_memB` recovers the bound from membership, and its
/// premise is LOAD-BEARING: at an index above the bound the premise is
/// `Bool.false = Bool.true` and no proof of it exists.
#[test]
fn lt_bound_of_mem_b_recovers_the_bound_and_needs_its_premise() {
    let mut f = Fixture::new();
    let p = f.p;
    let true_ = f.bool_true();

    // `singleton 2` has bound `3` and holds `2`.
    let s = f.singleton(2);
    let two = f.num(2);
    let witness = f.bool_refl(true_);
    let applied = f.const_app(p.finset_lt_bound_of_mem_b, &[s, two, witness]);
    let ty = match f.k.infer(applied) {
        Ok(t) => t,
        Err(e) => panic!("membership at 2 must compute to true: {}", f.explain(&e)),
    };
    let three = f.num(3);
    let expected = f.lt(two, three);
    assert!(
        f.k.def_eq(ty, expected),
        "the conclusion at (singleton 2, 2) must be 2 < 3, got {}",
        f.k.render_lean(ty)
    );
    let wrong = f.lt(three, two);
    assert!(
        !f.k.def_eq(ty, wrong),
        "negative control: the conclusion must NOT be 3 < 2 -- a statement \
         with the index and the bound transposed is indistinguishable \
         symbolically"
    );

    // NEGATIVE CONTROL, the sharper kind: at `5` the membership DECIDES to
    // `false`, so `Eq.refl true` is not a proof of the premise and the
    // application does not type-check at all.
    let five = f.num(5);
    let bad_witness = f.bool_refl(true_);
    let bad = f.const_app(p.finset_lt_bound_of_mem_b, &[s, five, bad_witness]);
    assert!(
        f.k.infer(bad).is_err(),
        "negative control: 5 is not a member of singleton 2, so the premise \
         must not be dischargeable by reflexivity"
    );
}

/// `Nat.Finset.card_le_of_injOn`'s conclusion at a CONCRETE pair of sets is the
/// hand-computed numeral bound `2 ≤ 4`, with both hypotheses left free.
///
/// The negative control is the reversed inequality: a `card_le_of_injOn` whose
/// two `card`s were transposed would type-check identically against free sets,
/// and only concrete numerals separate them.
#[test]
fn card_le_of_inj_on_states_the_numeral_bound_at_a_concrete_pair() {
    let mut f = Fixture::new();
    let p = f.p;

    let s = f.pair_set(1, 2); // card 2, bound 5
    let t = f.range(4); // card 4, bound 4
    let g = f.identity_map();

    let hinj_ty = f.inj_on_members(s, g);
    let hmaps_ty = f.maps_members(s, t, g);
    let (vars, mut ctx) = f.open(&[hinj_ty, hmaps_ty]);
    let applied = f.const_app(p.finset_card_le_of_inj_on, &[s, t, g, vars[0], vars[1]]);
    let inferred = match f.k.infer_in(applied, &mut ctx) {
        Ok(ty) => ty,
        Err(e) => panic!(
            "card_le_of_injOn must apply at ({{1,2}}, range 4, id): {}",
            f.explain(&e)
        ),
    };

    let two = f.num(2);
    let four = f.num(4);
    let expected = f.le(two, four);
    assert!(
        f.k.def_eq(inferred, expected),
        "the conclusion must be 2 <= 4, got {}",
        f.k.render_lean(inferred)
    );
    let wrong = f.le(four, two);
    assert!(
        !f.k.def_eq(inferred, wrong),
        "negative control: the conclusion must NOT be 4 <= 2"
    );

    // The two cards are what those numerals came from, checked independently so
    // a `card` that changed would fail here rather than shift the bound.
    let card_s = f.card(s);
    let card_t = f.card(t);
    let two_b = f.num(2);
    let four_b = f.num(4);
    assert!(f.k.def_eq(card_s, two_b), "card {{1,2}} must be 2");
    assert!(f.k.def_eq(card_t, four_b), "card (range 4) must be 4");
}

/// `Nat.Finset.pigeonhole` at a CONCRETE collapse: `{1,2}` has two members,
/// `{7}` has one, and the strict inequality `1 < 2` is discharged by
/// `Nat.le_refl 2` because `Lt 1 2` IS `Le 2 2`. What remains is a closed term
/// refuting injectivity.
///
/// TWO negative controls, on disjoint defect classes:
///
/// - the conclusion must be `False` and not `True` — a `pigeonhole` that
///   concluded anything else would still be admitted;
/// - at a codomain that is BIG ENOUGH (`range 3`, three members against two)
///   the strict inequality is `3 < 2` and the same witness does not
///   type-check, so the hypothesis is the load-bearing one rather than
///   decoration.
#[test]
fn pigeonhole_refutes_injectivity_at_a_concrete_collapse() {
    let mut f = Fixture::new();
    let p = f.p;

    let s = f.pair_set(1, 2); // card 2, bound 5
    let t = f.singleton(7); // card 1, bound 8
    let g = f.constant_map(7);

    let two = f.num(2);
    let hlt = f.lemma(p.le_refl_thm, &[two]);
    let hmaps_ty = f.maps_members(s, t, g);
    let hinj_ty = f.inj_on_members(s, g);
    let (vars, mut ctx) = f.open(&[hmaps_ty, hinj_ty]);
    let applied = f.const_app(p.finset_pigeonhole, &[s, t, g, hlt, vars[0], vars[1]]);
    let inferred = match f.k.infer_in(applied, &mut ctx) {
        Ok(ty) => ty,
        Err(e) => panic!(
            "pigeonhole must apply at ({{1,2}}, {{7}}, const 7): {}",
            f.explain(&e)
        ),
    };

    let false_ty = f.k.const_(p.logic.false_, vec![]);
    assert!(
        f.k.def_eq(inferred, false_ty),
        "the conclusion must be False, got {}",
        f.k.render_lean(inferred)
    );
    let true_ty = f.k.const_(p.logic.true_, vec![]);
    assert!(
        !f.k.def_eq(inferred, true_ty),
        "negative control: the conclusion must NOT be True"
    );

    // NEGATIVE CONTROL: a codomain at least as big as the domain. `card
    // (range 3) = 3`, so the strict inequality is `3 < 2`, i.e. `Le 4 2`, and
    // `Nat.le_refl 2 : Le 2 2` is not a proof of it.
    let big = f.range(3);
    let two_b = f.num(2);
    let bad_hlt = f.lemma(p.le_refl_thm, &[two_b]);
    let bad_maps_ty = f.maps_members(s, big, g);
    let bad_inj_ty = f.inj_on_members(s, g);
    let (bad_vars, mut bad_ctx) = f.open(&[bad_maps_ty, bad_inj_ty]);
    let bad = f.const_app(
        p.finset_pigeonhole,
        &[s, big, g, bad_hlt, bad_vars[0], bad_vars[1]],
    );
    assert!(
        f.k.infer_in(bad, &mut bad_ctx).is_err(),
        "negative control: with three pigeonholes for two pigeons the strict \
         inequality must not be dischargeable"
    );
}

/// `Nat.Finset.allBelow_false_witness` turns a `false` bounded loop into an
/// index, and the SEARCH is what makes it constructive here: there is no
/// choice principle in this kernel, so the witness is computed by the
/// recursion.
///
/// `allBelow (3 ≤ ·) 5` computes to `false` (index `0` already fails), and the
/// resulting statement is the `Exists` rebuilt independently below. The
/// negative control is `fun _ => true`, whose loop computes to `true`: the
/// premise is then `Bool.true = Bool.false` and the application does not
/// type-check.
#[test]
fn all_below_false_witness_needs_a_false_loop_and_states_the_search() {
    let mut f = Fixture::new();
    let p = f.p;
    let nat = f.nat_ty();
    let fal = f.bool_false();

    let pred = f.at_least(3);
    let five = f.num(5);

    // The loop really is `false` — the fact the premise reflects.
    let loop_ = f.const_app(p.finset_all_below, &[pred, five]);
    assert!(
        f.k.def_eq(loop_, fal),
        "allBelow (3 <= .) 5 must be false -- index 0 already fails"
    );
    let true_ = f.bool_true();
    assert!(
        !f.k.def_eq(loop_, true_),
        "negative control: allBelow (3 <= .) 5 must NOT be true"
    );

    let witness = f.bool_refl(fal);
    let applied = f.const_app(p.finset_all_below_false_witness, &[pred, five, witness]);
    let inferred = match f.k.infer(applied) {
        Ok(ty) => ty,
        Err(e) => panic!("the loop computes to false, so this must apply: {e:?}"),
    };

    let expected = {
        let i_fv = f.fresh_fvar();
        let i = f.k.fvar(i_fv);
        let five_b = f.num(5);
        let lt = f.lt(i, five_b);
        let pi = f.apply(pred, &[i]);
        let fal_b = f.bool_false();
        let is_false = f.bool_eq(pi, fal_b);
        let body = f.and_of(lt, is_false);
        let lam = f.lam_fv(i_fv, nat, body);
        f.exists_nat(lam)
    };
    assert!(
        f.k.def_eq(inferred, expected),
        "the statement must be an index below 5 at which the predicate is \
         FALSE, got {}",
        f.k.render_lean(inferred)
    );

    let wrong = {
        // The same shape with `true` in place of `false`: a witness lemma that
        // returned an index where the predicate HOLDS would be a different
        // theorem, and one no `false` loop can supply.
        let i_fv = f.fresh_fvar();
        let i = f.k.fvar(i_fv);
        let five_b = f.num(5);
        let lt = f.lt(i, five_b);
        let pi = f.apply(pred, &[i]);
        let true_b = f.bool_true();
        let is_true = f.bool_eq(pi, true_b);
        let body = f.and_of(lt, is_true);
        let lam = f.lam_fv(i_fv, nat, body);
        f.exists_nat(lam)
    };
    assert!(
        !f.k.def_eq(inferred, wrong),
        "negative control: the witness must be an index where the predicate \
         is FALSE, not one where it is true"
    );

    // NEGATIVE CONTROL: a loop that computes to `true` cannot supply the
    // premise at all.
    let always = f.always_true();
    let five_c = f.num(5);
    let fal_c = f.bool_false();
    let bad_witness = f.bool_refl(fal_c);
    let bad = f.const_app(
        p.finset_all_below_false_witness,
        &[always, five_c, bad_witness],
    );
    assert!(
        f.k.infer(bad).is_err(),
        "negative control: allBelow (fun _ => true) 5 is true, so the premise \
         must not be dischargeable"
    );
}

/// `Nat.Finset.exists_collision` is the STRONG form: its conclusion names two
/// indices, asserts both are members, asserts they are DISTINCT, and asserts
/// their images agree.
///
/// The distinctness conjunct is the whole content — an "`exists_collision`"
/// that dropped it would be trivially true at `a = b` for any member at all,
/// would be admitted by the kernel, and would carry an empty axiom footprint.
/// So the negative control here is exactly that weakened statement, rebuilt and
/// required NOT to match.
#[test]
fn exists_collision_states_a_distinct_pair_with_equal_images() {
    let mut f = Fixture::new();
    let p = f.p;
    let nat = f.nat_ty();

    let s = f.pair_set(1, 2); // card 2, bound 5
    let t = f.singleton(7); // card 1, bound 8
    let g = f.constant_map(7);

    let two = f.num(2);
    let hlt = f.lemma(p.le_refl_thm, &[two]);
    let hmaps_ty = f.maps_members(s, t, g);
    let (vars, mut ctx) = f.open(&[hmaps_ty]);
    let applied = f.const_app(p.finset_exists_collision, &[s, t, g, hlt, vars[0]]);
    let inferred = match f.k.infer_in(applied, &mut ctx) {
        Ok(ty) => ty,
        Err(e) => panic!(
            "exists_collision must apply at ({{1,2}}, {{7}}, const 7): {}",
            f.explain(&e)
        ),
    };

    let pair_statement = |f: &mut Fixture, distinct: bool| -> ExprId {
        let true_ = f.bool_true();
        let a_fv = f.fresh_fvar();
        let a = f.k.fvar(a_fv);
        let inner = {
            let b_fv = f.fresh_fvar();
            let b = f.k.fvar(b_fv);
            let ga = f.apply(g, &[a]);
            let gb = f.apply(g, &[b]);
            let same = f.eq(ga, gb);
            let tail = if distinct {
                let eq_ab = f.eq(a, b);
                let not_name = f.p.logic.not;
                let ne = f.const_app(not_name, &[eq_ab]);
                f.and_of(ne, same)
            } else {
                same
            };
            let mb = f.memb_at(s, b);
            let sel_b = f.bool_eq(mb, true_);
            let with_b = f.and_of(sel_b, tail);
            let ma = f.memb_at(s, a);
            let sel_a = f.bool_eq(ma, true_);
            let body = f.and_of(sel_a, with_b);
            let lam = f.lam_fv(b_fv, nat, body);
            f.exists_nat(lam)
        };
        let lam = f.lam_fv(a_fv, nat, inner);
        f.exists_nat(lam)
    };

    let expected = pair_statement(&mut f, true);
    assert!(
        f.k.def_eq(inferred, expected),
        "the conclusion must name two members with equal images that are \
         DISTINCT, got {}",
        f.k.render_lean(inferred)
    );

    let weakened = pair_statement(&mut f, false);
    assert!(
        !f.k.def_eq(inferred, weakened),
        "negative control: dropping the distinctness conjunct gives a \
         statement that is trivially true at a = b, and it must NOT be what \
         exists_collision says"
    );

    // And the strict inequality is load-bearing here too: with `range 3` as the
    // codomain there is no collapse and the witness does not type-check.
    let big = f.range(3);
    let two_b = f.num(2);
    let bad_hlt = f.lemma(p.le_refl_thm, &[two_b]);
    let bad_maps_ty = f.maps_members(s, big, g);
    let (bad_vars, mut bad_ctx) = f.open(&[bad_maps_ty]);
    let bad = f.const_app(
        p.finset_exists_collision,
        &[s, big, g, bad_hlt, bad_vars[0]],
    );
    assert!(
        f.k.infer_in(bad, &mut bad_ctx).is_err(),
        "negative control: with three pigeonholes for two pigeons there is no \
         collision to produce"
    );
}
