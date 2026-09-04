//! Tests for `nat_prelude::omniscience` — the reverse-mathematics map's
//! omniscience principles (roadmap W1-9).
//!
//! A separate file rather than an addition to the dense `nat_prelude_tests.rs`,
//! for the merge hazard `avg_pair_tests.rs` records. `Fixture` is a small local
//! copy of `nat_prelude_tests::Fixture` (that one is module-private).
//!
//! **What could go wrong here, and what each test rules out.** Every
//! declaration in `omniscience.rs` is a *theorem*, so `add_declaration` already
//! rejects a wrong proof. What it cannot reject is a wrong *statement*: an
//! implication whose hypothesis is stronger than advertised, or whose
//! conclusion is weaker, type-checks perfectly and proves nothing. So the
//! tests here are all of one shape — **apply the theorem at genuinely FREE
//! variables of the advertised hypothesis type and check the inferred
//! conclusion on the nose**, then feed the hypothesis slot something the
//! prelude *already has* and require rejection. Numerals reduce and hide
//! definitional-equality gaps, so nothing here instantiates a sequence
//! concretely.

use crate::env::Declaration;
use crate::expr::ExprId;
use crate::name::NameId;
use crate::{
    BinderInfo, Kernel, LocalContext, LocalDecl, NatOps, NatPrelude, NatState, build_nat_prelude,
};

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

    fn explain_err(&mut self, e: &crate::KernelError) -> String {
        NatOps::explain(self, e)
    }
}

// --- the principles, rebuilt independently of `omniscience.rs` --------------
//
// These builders are DELIBERATELY a second implementation. If they simply
// called the module's own private helpers, every check below would compare a
// term with itself and could not fail.

fn seq_ty(f: &mut Fixture) -> ExprId {
    let nat = f.nat_ty();
    let b = f.bool_ty();
    f.arrow(nat, b)
}

fn hits_ty(f: &mut Fixture, seq: ExprId) -> ExprId {
    let p = f.p;
    let nat = f.nat_ty();
    let one = f.level_one();
    let pred = {
        let n_fv = f.fresh_fvar();
        let n = f.k.fvar(n_fv);
        let applied = f.apply(seq, &[n]);
        let t = f.bool_true();
        let body = f.bool_eq(applied, t);
        f.lam_fv(n_fv, nat, body)
    };
    let ex = f.k.const_(p.logic.exists_, vec![one]);
    f.apply(ex, &[nat, pred])
}

fn misses_ty(f: &mut Fixture, seq: ExprId) -> ExprId {
    let nat = f.nat_ty();
    let n_fv = f.fresh_fvar();
    let n = f.k.fvar(n_fv);
    let applied = f.apply(seq, &[n]);
    let fa = f.bool_false();
    let body = f.bool_eq(applied, fa);
    f.pi_fv(n_fv, nat, body)
}

fn not_ty(f: &mut Fixture, a: ExprId) -> ExprId {
    let p = f.p;
    f.const_app(p.logic.not, &[a])
}

fn lpo_ty(f: &mut Fixture) -> ExprId {
    let p = f.p;
    let sty = seq_ty(f);
    let g_fv = f.fresh_fvar();
    let g = f.k.fvar(g_fv);
    let h = hits_ty(f, g);
    let m = misses_ty(f, g);
    let body = f.const_app(p.logic.or, &[h, m]);
    f.pi_fv(g_fv, sty, body)
}

fn wlpo_ty(f: &mut Fixture) -> ExprId {
    let p = f.p;
    let sty = seq_ty(f);
    let g_fv = f.fresh_fvar();
    let g = f.k.fvar(g_fv);
    let m = misses_ty(f, g);
    let nm = not_ty(f, m);
    let body = f.const_app(p.logic.or, &[m, nm]);
    f.pi_fv(g_fv, sty, body)
}

fn markov_ty(f: &mut Fixture) -> ExprId {
    let sty = seq_ty(f);
    let g_fv = f.fresh_fvar();
    let g = f.k.fvar(g_fv);
    let m = misses_ty(f, g);
    let nm = not_ty(f, m);
    let h = hits_ty(f, g);
    let body = f.arrow(nm, h);
    f.pi_fv(g_fv, sty, body)
}

/// `∀ (Q : Nat → Prop), (∃ n, Q n) → ∃ m, And (Q m) (∀ k, Lt k m → Not (Q k))`
/// — the unrestricted least-number principle, a THIRD independent spelling
/// (`least_number.rs` and `omniscience.rs` hold the other two).
fn unrestricted_lnp_ty(f: &mut Fixture) -> ExprId {
    let p = f.p;
    let nat = f.nat_ty();
    let prop = f.k.sort_zero();
    let one = f.level_one();
    let pty = f.arrow(nat, prop);

    let q_fv = f.fresh_fvar();
    let q = f.k.fvar(q_fv);

    let inhabited = {
        let n_fv = f.fresh_fvar();
        let n = f.k.fvar(n_fv);
        let body = f.apply(q, &[n]);
        let pred = f.lam_fv(n_fv, nat, body);
        let ex = f.k.const_(p.logic.exists_, vec![one]);
        f.apply(ex, &[nat, pred])
    };
    let least = {
        let m_fv = f.fresh_fvar();
        let m = f.k.fvar(m_fv);
        let qm = f.apply(q, &[m]);
        let none_below = {
            let k_fv = f.fresh_fvar();
            let kk = f.k.fvar(k_fv);
            let lt = f.lt(kk, m);
            let qk = f.apply(q, &[kk]);
            let nqk = not_ty(f, qk);
            let imp = f.arrow(lt, nqk);
            f.pi_fv(k_fv, nat, imp)
        };
        let body = f.const_app(p.logic.and, &[qm, none_below]);
        let pred = f.lam_fv(m_fv, nat, body);
        let ex = f.k.const_(p.logic.exists_, vec![one]);
        f.apply(ex, &[nat, pred])
    };
    let body = f.arrow(inhabited, least);
    f.pi_fv(q_fv, pty, body)
}

fn excluded_middle_ty(f: &mut Fixture) -> ExprId {
    let p = f.p;
    let prop = f.k.sort_zero();
    let x_fv = f.fresh_fvar();
    let x = f.k.fvar(x_fv);
    let nx = not_ty(f, x);
    let body = f.const_app(p.logic.or, &[x, nx]);
    f.pi_fv(x_fv, prop, body)
}

/// Push one free variable of type `ty` into a fresh context and return it.
fn free_of(f: &mut Fixture, ctx: &mut LocalContext, ty: ExprId) -> ExprId {
    let anon = f.k.anon();
    let fv = f.fresh_fvar();
    ctx.push(LocalDecl {
        fvar: fv,
        name: anon,
        ty,
        info: BinderInfo::Default,
    });
    f.k.fvar(fv)
}

// --- the six declarations exist, and are axiom-free -------------------------

/// The six names are admitted, all as `Theorem`s, all with an EMPTY
/// `Kernel::axiom_footprint`.
///
/// This is the claim the whole ADR-1601 measurement rests on — the classical
/// principles enter as hypotheses, so the trusted base does not move. It is
/// read from `axiom_footprint`, never from a rendered name.
#[test]
fn the_omniscience_map_is_admitted_and_axiom_free() {
    let f = Fixture::new();
    let p = f.p;
    let names = [
        p.omniscience.em_implies_lpo,
        p.omniscience.lpo_implies_wlpo,
        p.omniscience.lpo_implies_markov,
        p.omniscience.lpo_implies_llpo,
        p.omniscience.wlpo_and_markov_imply_lpo,
        p.omniscience.lnp_unrestricted_implies_lpo,
    ];
    assert_eq!(names.len(), 6, "the map has six edges");
    for name in names {
        let shown = f.k.display_name(name).to_string();
        let decl =
            f.k.environment()
                .get(name)
                .unwrap_or_else(|| panic!("{shown} must be admitted"))
                .clone();
        assert!(
            matches!(decl, Declaration::Theorem { .. }),
            "{shown} must be a Theorem, not {decl:?}"
        );
        let footprint = f.k.axiom_footprint(name);
        assert!(
            footprint.is_empty(),
            "{shown} must be axiom-free, found {:?}",
            footprint
                .iter()
                .map(|n| f.k.display_name(*n).to_string())
                .collect::<Vec<_>>()
        );
    }
}

// --- EM -> LPO --------------------------------------------------------------

/// `Nat.em_implies_lpo` applied to a FREE excluded-middle hypothesis and a
/// FREE sequence yields exactly `Or (Hits f) (Misses f)`.
///
/// NEGATIVE CONTROL: `Nat.lnp_of_pointwise_decision` — a theorem this prelude
/// actually has, and the closest thing in it to a decision principle — must
/// NOT discharge the excluded-middle slot. Without that, the test would pass
/// for a statement whose hypothesis is already proved, i.e. for a proof of
/// LPO.
#[test]
fn em_implies_lpo_applies_at_a_free_hypothesis_and_a_free_sequence() {
    let mut f = Fixture::new();
    let p = f.p;
    let mut ctx = LocalContext::new();

    let em_ty = excluded_middle_ty(&mut f);
    let em = free_of(&mut f, &mut ctx, em_ty);
    let sty = seq_ty(&mut f);
    let seq = free_of(&mut f, &mut ctx, sty);

    let applied = f.const_app(p.omniscience.em_implies_lpo, &[em, seq]);
    let inferred =
        f.k.infer_in(applied, &mut ctx)
            .unwrap_or_else(|err| panic!("EM -> LPO must apply: {}", f.explain_err(&err)));

    let h = hits_ty(&mut f, seq);
    let m = misses_ty(&mut f, seq);
    let expected = f.const_app(p.logic.or, &[h, m]);
    assert!(
        f.k.def_eq_in(inferred, expected, &mut ctx),
        "conclusion must be `Or (Hits f) (Misses f)`, found {}",
        f.k.render_lean(inferred)
    );

    let already_proved = f.k.const_(p.lnp_of_pointwise_decision, vec![]);
    let bogus = f.const_app(p.omniscience.em_implies_lpo, &[already_proved, seq]);
    assert!(
        f.k.infer_in(bogus, &mut ctx).is_err(),
        "an existing theorem must NOT discharge the excluded-middle hypothesis"
    );
}

// --- LPO -> WLPO / MP / LLPO ------------------------------------------------

/// `Nat.lpo_implies_wlpo` at a free LPO hypothesis lands on
/// `Or (Misses f) (Not (Misses f))` — the *decision*, with no witness.
///
/// NEGATIVE CONTROL: the WLPO term itself must not be accepted in LPO's slot.
/// The two differ only in the first disjunct (`Hits f` vs `Misses f`), which is
/// exactly the distinction the whole map turns on, and it is a SMALL term
/// difference — one subterm of one disjunct.
#[test]
fn lpo_implies_wlpo_lands_on_the_decision_and_rejects_wlpo_in_its_own_slot() {
    let mut f = Fixture::new();
    let p = f.p;
    let mut ctx = LocalContext::new();

    let lpo = lpo_ty(&mut f);
    let hlpo = free_of(&mut f, &mut ctx, lpo);
    let sty = seq_ty(&mut f);
    let seq = free_of(&mut f, &mut ctx, sty);

    let applied = f.const_app(p.omniscience.lpo_implies_wlpo, &[hlpo, seq]);
    let inferred =
        f.k.infer_in(applied, &mut ctx)
            .unwrap_or_else(|err| panic!("LPO -> WLPO must apply: {}", f.explain_err(&err)));

    let m = misses_ty(&mut f, seq);
    let nm = not_ty(&mut f, m);
    let expected = f.const_app(p.logic.or, &[m, nm]);
    assert!(
        f.k.def_eq_in(inferred, expected, &mut ctx),
        "conclusion must be `Or (Misses f) (Not (Misses f))`, found {}",
        f.k.render_lean(inferred)
    );

    let wlpo = wlpo_ty(&mut f);
    let hwlpo = free_of(&mut f, &mut ctx, wlpo);
    let bogus = f.const_app(p.omniscience.lpo_implies_wlpo, &[hwlpo, seq]);
    assert!(
        f.k.infer_in(bogus, &mut ctx).is_err(),
        "WLPO must NOT discharge LPO's slot -- if it does, the edge is trivial"
    );
}

/// `Nat.lpo_implies_markov` at free hypotheses lands on `Hits f`, the WITNESS.
///
/// NEGATIVE CONTROL: WLPO in LPO's slot must be rejected. WLPO plus Markov is
/// LPO (`wlpo_and_markov_imply_lpo`), so if WLPO alone could discharge this
/// slot the map would have collapsed.
#[test]
fn lpo_implies_markov_lands_on_the_witness_and_rejects_wlpo_in_its_own_slot() {
    let mut f = Fixture::new();
    let p = f.p;
    let mut ctx = LocalContext::new();

    let lpo = lpo_ty(&mut f);
    let hlpo = free_of(&mut f, &mut ctx, lpo);
    let sty = seq_ty(&mut f);
    let seq = free_of(&mut f, &mut ctx, sty);
    let m = misses_ty(&mut f, seq);
    let nm = not_ty(&mut f, m);
    let hnm = free_of(&mut f, &mut ctx, nm);

    let applied = f.const_app(p.omniscience.lpo_implies_markov, &[hlpo, seq, hnm]);
    let inferred =
        f.k.infer_in(applied, &mut ctx)
            .unwrap_or_else(|err| panic!("LPO -> MP must apply: {}", f.explain_err(&err)));

    let expected = hits_ty(&mut f, seq);
    assert!(
        f.k.def_eq_in(inferred, expected, &mut ctx),
        "conclusion must be `Hits f`, found {}",
        f.k.render_lean(inferred)
    );

    let wlpo = wlpo_ty(&mut f);
    let hwlpo = free_of(&mut f, &mut ctx, wlpo);
    let bogus = f.const_app(p.omniscience.lpo_implies_markov, &[hwlpo, seq, hnm]);
    assert!(
        f.k.infer_in(bogus, &mut ctx).is_err(),
        "WLPO alone must NOT discharge LPO's slot in Markov's derivation"
    );
}

/// `Nat.lpo_implies_llpo` at free hypotheses lands on `Or (Misses f) (Misses g)`
/// — and, crucially, it needs the `Not (And (Hits f) (Hits g))` premise.
///
/// NEGATIVE CONTROL: `Not (And (Misses f) (Misses g))` — the SAME term with
/// `Hits` replaced by `Misses` in both conjuncts, a small and local change —
/// must be rejected in the premise slot.
#[test]
fn lpo_implies_llpo_needs_the_disjointness_premise_as_stated() {
    let mut f = Fixture::new();
    let p = f.p;
    let mut ctx = LocalContext::new();

    let lpo = lpo_ty(&mut f);
    let hlpo = free_of(&mut f, &mut ctx, lpo);
    let sty = seq_ty(&mut f);
    let sq_f = free_of(&mut f, &mut ctx, sty);
    let sq_g = free_of(&mut f, &mut ctx, sty);

    let hf = hits_ty(&mut f, sq_f);
    let hg = hits_ty(&mut f, sq_g);
    let both = f.const_app(p.logic.and, &[hf, hg]);
    let nboth = not_ty(&mut f, both);
    let hno = free_of(&mut f, &mut ctx, nboth);

    let applied = f.const_app(p.omniscience.lpo_implies_llpo, &[hlpo, sq_f, sq_g, hno]);
    let inferred =
        f.k.infer_in(applied, &mut ctx)
            .unwrap_or_else(|err| panic!("LPO -> LLPO must apply: {}", f.explain_err(&err)));

    let mf = misses_ty(&mut f, sq_f);
    let mg = misses_ty(&mut f, sq_g);
    let expected = f.const_app(p.logic.or, &[mf, mg]);
    assert!(
        f.k.def_eq_in(inferred, expected, &mut ctx),
        "conclusion must be `Or (Misses f) (Misses g)`, found {}",
        f.k.render_lean(inferred)
    );

    let mf2 = misses_ty(&mut f, sq_f);
    let mg2 = misses_ty(&mut f, sq_g);
    let wrong_and = f.const_app(p.logic.and, &[mf2, mg2]);
    let wrong = not_ty(&mut f, wrong_and);
    let hwrong = free_of(&mut f, &mut ctx, wrong);
    let bogus = f.const_app(p.omniscience.lpo_implies_llpo, &[hlpo, sq_f, sq_g, hwrong]);
    assert!(
        f.k.infer_in(bogus, &mut ctx).is_err(),
        "the premise must be `Not (And (Hits f) (Hits g))`, not the `Misses` form"
    );
}

// --- the converse edge ------------------------------------------------------

/// `Nat.wlpo_and_markov_imply_lpo` — the edge that makes this a map rather
/// than a chain — lands on `Or (Hits f) (Misses f)`.
///
/// NEGATIVE CONTROL: WLPO in Markov's slot must be rejected. If it were
/// accepted, WLPO alone would imply LPO and the entire distinction between
/// this file's four principles would be empty.
#[test]
fn wlpo_and_markov_imply_lpo_needs_both_and_rejects_wlpo_twice() {
    let mut f = Fixture::new();
    let p = f.p;
    let mut ctx = LocalContext::new();

    let wlpo = wlpo_ty(&mut f);
    let hwlpo = free_of(&mut f, &mut ctx, wlpo);
    let mp = markov_ty(&mut f);
    let hmp = free_of(&mut f, &mut ctx, mp);
    let sty = seq_ty(&mut f);
    let seq = free_of(&mut f, &mut ctx, sty);

    let applied = f.const_app(p.omniscience.wlpo_and_markov_imply_lpo, &[hwlpo, hmp, seq]);
    let inferred =
        f.k.infer_in(applied, &mut ctx)
            .unwrap_or_else(|err| panic!("WLPO + MP -> LPO must apply: {}", f.explain_err(&err)));

    let h = hits_ty(&mut f, seq);
    let m = misses_ty(&mut f, seq);
    let expected = f.const_app(p.logic.or, &[h, m]);
    assert!(
        f.k.def_eq_in(inferred, expected, &mut ctx),
        "conclusion must be `Or (Hits f) (Misses f)`, found {}",
        f.k.render_lean(inferred)
    );

    let hwlpo2 = free_of(&mut f, &mut ctx, wlpo);
    let bogus = f.const_app(
        p.omniscience.wlpo_and_markov_imply_lpo,
        &[hwlpo, hwlpo2, seq],
    );
    assert!(
        f.k.infer_in(bogus, &mut ctx).is_err(),
        "WLPO must NOT discharge Markov's slot -- otherwise WLPO alone gives LPO"
    );
}

// --- the join to the existing calibration point -----------------------------

/// `Nat.lnp_unrestricted_implies_lpo` joins the new map to
/// `least_number.rs`'s EM ↔ unrestricted-LNP point.
///
/// Its ADMISSION already proves something the source alone does not: the
/// unrestricted-LNP term rebuilt in `omniscience.rs` is definitionally the one
/// `least_number.rs` declared, because the proof applies
/// `Nat.lnp_unrestricted_implies_em` to it.
///
/// NEGATIVE CONTROL: `Nat.lnp_of_pointwise_decision` — the SAME statement with
/// one extra decidability hypothesis, and a theorem this prelude has — must not
/// discharge the unrestricted slot.
#[test]
fn lnp_unrestricted_implies_lpo_applies_the_existing_lnp_theorem() {
    let mut f = Fixture::new();
    let p = f.p;
    let mut ctx = LocalContext::new();

    // The hypothesis type is rebuilt HERE, independently of `omniscience.rs`
    // and of `least_number.rs`. If the three spellings of the unrestricted
    // least-number principle disagree, this application fails to infer -- so
    // the positive half of this test is itself the agreement check.
    let lnp = unrestricted_lnp_ty(&mut f);
    let hlnp = free_of(&mut f, &mut ctx, lnp);
    let sty = seq_ty(&mut f);
    let seq = free_of(&mut f, &mut ctx, sty);

    let applied = f.const_app(p.omniscience.lnp_unrestricted_implies_lpo, &[hlnp, seq]);
    let inferred =
        f.k.infer_in(applied, &mut ctx)
            .unwrap_or_else(|err| panic!("LNP -> LPO must apply: {}", f.explain_err(&err)));

    let h = hits_ty(&mut f, seq);
    let m = misses_ty(&mut f, seq);
    let expected = f.const_app(p.logic.or, &[h, m]);
    assert!(
        f.k.def_eq_in(inferred, expected, &mut ctx),
        "conclusion must be `Or (Hits f) (Misses f)`, found {}",
        f.k.render_lean(inferred)
    );

    let decidable = f.k.const_(p.lnp_of_pointwise_decision, vec![]);
    let bogus = f.const_app(
        p.omniscience.lnp_unrestricted_implies_lpo,
        &[decidable, seq],
    );
    assert!(
        f.k.infer_in(bogus, &mut ctx).is_err(),
        "the decidable form must NOT discharge the unrestricted hypothesis"
    );
}

// --- non-vacuity: none of the four principles is already a declaration ------

/// **None of LPO, WLPO, Markov's principle or LLPO is itself declared
/// anywhere in the environment.**
///
/// Every implication above would be worthless if its hypothesis were lying
/// around as a theorem. The POSITIVE CONTROL runs the identical scan for the
/// type of `Nat.em_implies_lpo` and requires exactly one hit, so a scan that
/// has stopped matching anything fails the test rather than reporting a clean
/// zero.
#[test]
fn no_omniscience_principle_is_itself_declared() {
    let mut f = Fixture::new();

    let candidates: Vec<(&str, ExprId)> = {
        let a = lpo_ty(&mut f);
        let b = wlpo_ty(&mut f);
        let c = markov_ty(&mut f);
        let d = excluded_middle_ty(&mut f);
        vec![("LPO", a), ("WLPO", b), ("Markov", c), ("EM", d)]
    };
    let control_ty = {
        let em = excluded_middle_ty(&mut f);
        let lpo = lpo_ty(&mut f);
        f.arrow(em, lpo)
    };

    let declared: Vec<(NameId, Declaration)> =
        f.k.environment()
            .iter()
            .map(|(name, decl)| (*name, decl.clone()))
            .collect();
    let ty_of = |decl: &Declaration| -> Option<ExprId> {
        match decl {
            Declaration::Theorem { ty, .. }
            | Declaration::Definition { ty, .. }
            | Declaration::Axiom { ty, .. }
            | Declaration::Opaque { ty, .. } => Some(*ty),
            _ => None,
        }
    };

    let control: Vec<String> = declared
        .iter()
        .filter(|(_, decl)| ty_of(decl) == Some(control_ty))
        .map(|(name, _)| f.k.display_name(*name).to_string())
        .collect();
    assert_eq!(
        control.len(),
        1,
        "POSITIVE CONTROL: the scan must find exactly `Nat.em_implies_lpo` by \
         its type; found {control:?}. A zero here means the scan is broken, not \
         that the principles are absent."
    );

    for (label, ty) in candidates {
        let holders: Vec<String> = declared
            .iter()
            .filter(|(_, decl)| ty_of(decl) == Some(ty))
            .map(|(name, _)| f.k.display_name(*name).to_string())
            .collect();
        assert!(
            holders.is_empty(),
            "{label} is already declared as {holders:?} -- every implication \
             taking it as a hypothesis would then be vacuous"
        );
    }
}
