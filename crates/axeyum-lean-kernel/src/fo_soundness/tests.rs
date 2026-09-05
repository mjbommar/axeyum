//! Tests for `fo_soundness.rs`.
//!
//! The kernel admitting `FO.soundness` is the mathematical check. What these
//! tests add is (a) axiom-freedom, after `Environment::contains`, (b) that
//! `FO.soundness`'s statement is the one claimed rather than a weaker
//! provable relative, and (c) that it *instantiates* — applied to the three
//! example derivations of `fo_provable.rs` at the ℕ structure, it produces the
//! satisfaction facts it should.
//!
//! (c) matters because a soundness theorem quantified over an inhabited-looking
//! but unusable family would still admit. Pushing a real derivation through it
//! and reading the result back is the positive control.

use super::*;
use crate::Kernel;

struct Fixture {
    kernel: Kernel,
    p: FoSoundnessPrelude,
}

impl Fixture {
    fn new() -> Self {
        let mut kernel = Kernel::new();
        let p = build_fo_soundness_prelude(&mut kernel).expect("FO soundness prelude must build");
        Self { kernel, p }
    }

    fn env(&mut self) -> SoundEnv {
        let calculus = self.p.calculus;
        let subst = self.p.substitution;
        SoundEnv::new(&mut self.kernel, &calculus, &subst)
    }

    fn nat_ty(&mut self) -> ExprId {
        self.kernel
            .const_(self.p.calculus.semantics.syntax.nat.nat, vec![])
    }

    fn nat_structure(&mut self) -> ExprId {
        self.kernel
            .const_(self.p.calculus.semantics.nat_structure, vec![])
    }
}

/// The three theorems are declared and axiom-free.
#[test]
fn soundness_and_its_corollary_are_axiom_free() {
    let f = Fixture::new();
    let p = f.p;
    let kernel = f.kernel;
    for (name, label) in [
        (p.ctx_sat_shift, "FO.ctxSat_shift"),
        (p.soundness, "FO.soundness"),
        (p.consistency, "FO.consistency"),
    ] {
        assert!(
            kernel.environment().contains(name),
            "{label} must be in the environment before its footprint means anything"
        );
        let footprint = kernel.axiom_footprint(name);
        assert!(
            footprint.is_empty(),
            "{label} must be axiom-free; it depends on {footprint:?}"
        );
    }
}

/// `FO.soundness`'s inferred type is
/// `Π M S g p, Provable g p -> Π w, ctxSat M S g w -> sat M S p w`, rebuilt
/// here from `FO.Provable`, `FO.ctxSat` and `FO.sat`.
///
/// The negative control is the version with the hypothesis dropped —
/// `Π M S g p, Provable g p -> Π w, sat M S p w` — which is the statement a
/// soundness theorem that ignored its context would have, and which is FALSE
/// (`Provable (cons a nil) a` holds for every `a`).
#[test]
fn soundness_states_the_theorem_it_claims() {
    let mut f = Fixture::new();
    let e = f.env();

    let g_id = 1_645_001_u64;
    let p_id = 1_645_002_u64;
    let d_id = 1_645_003_u64;
    let w_id = 1_645_004_u64;
    let g = f.kernel.fvar(g_id);
    let p = f.kernel.fvar(p_id);
    let w = f.kernel.fvar(w_id);

    let deriv_ty = {
        let c = f.kernel.const_(e.calc.provable, vec![]);
        apply_all(&mut f.kernel, c, &[g, p])
    };

    let build = |f: &mut Fixture, with_hypothesis: bool| -> ExprId {
        let concl = sat_of(&mut f.kernel, &e, p, w);
        let inner = if with_hypothesis {
            let hyp = ctx_sat_of(&mut f.kernel, &e, g, w);
            arrow(&mut f.kernel, hyp, concl)
        } else {
            concl
        };
        let carrier = pi_fv(&mut f.kernel, w_id, e.val_ty, inner);
        let body = pis(
            &mut f.kernel,
            &[
                (g_id, e.calc.context_ty),
                (p_id, e.calc.formula_ty),
                (d_id, deriv_ty),
            ],
            carrier,
        );
        pis(
            &mut f.kernel,
            &[(e.m_id, e.type_sort), (e.s_id, e.struct_m)],
            body,
        )
    };

    let c = f.kernel.const_(f.p.soundness, vec![]);
    let got = f.kernel.infer(c).expect("must infer");

    let want = build(&mut f, true);
    assert!(
        f.kernel.def_eq(got, want),
        "FO.soundness's type: got {}, want {}",
        f.kernel.render_lean(got),
        f.kernel.render_lean(want)
    );

    let context_free = build(&mut f, false);
    assert!(
        !f.kernel.def_eq(got, context_free),
        "FO.soundness must consume its context-satisfaction hypothesis"
    );
}

/// `FO.consistency`'s type is `Not (FO.Provable FO.Context.nil FO.Formula.bot)`
/// and nothing weaker.
#[test]
fn consistency_states_the_underivability_of_bot() {
    let mut f = Fixture::new();
    let e = f.env();

    let nil = f.kernel.const_(e.calc.nil, vec![]);
    let bot = f.kernel.const_(e.calc.bot, vec![]);
    let deriv_ty = {
        let c = f.kernel.const_(e.calc.provable, vec![]);
        apply_all(&mut f.kernel, c, &[nil, bot])
    };
    let want = {
        let not_const = f.kernel.const_(e.logic.not, vec![]);
        f.kernel.app(not_const, deriv_ty)
    };

    let c = f.kernel.const_(f.p.consistency, vec![]);
    let got = f.kernel.infer(c).expect("must infer");
    assert!(
        f.kernel.def_eq(got, want),
        "FO.consistency's type: got {}, want {}",
        f.kernel.render_lean(got),
        f.kernel.render_lean(want)
    );
}

/// **Soundness instantiates.** Pushing `FO.provable_all_imp_ex` — the
/// genuinely first-order example derivation, `⊢ (∀x. R(x)) → (∃x. R(x))` —
/// through `FO.soundness` at the ℕ structure yields a term whose type is the
/// satisfaction of that implication at every valuation.
///
/// A soundness theorem that could not be applied to a real derivation would
/// still admit; this is the check that it can be.
#[test]
fn soundness_applies_to_the_first_order_example_derivation() {
    let mut f = Fixture::new();
    let e = f.env();
    let nat_ty = f.nat_ty();
    let structure = f.nat_structure();

    let nil = f.kernel.const_(e.calc.nil, vec![]);
    let derivation = f.kernel.const_(f.p.calculus.provable_all_imp_ex, vec![]);
    // The derivation's type is `Provable nil φ`; φ is rebuilt here the same way
    // `fo_provable.rs` builds it, so the application below is not merely
    // whatever the declaration happens to say.
    let syn = f.p.calculus.semantics.syntax.names(&mut f.kernel);
    let phi = {
        let zero = f.kernel.const_(syn.nat_zero, vec![]);
        let var = f.kernel.const_(syn.var, vec![]);
        let v0 = f.kernel.app(var, zero);
        let zero2 = f.kernel.const_(syn.nat_zero, vec![]);
        let rel1 = f.kernel.const_(syn.rel1, vec![]);
        let atom = apply_all(&mut f.kernel, rel1, &[zero2, v0]);
        let all_c = f.kernel.const_(syn.all, vec![]);
        let universal = f.kernel.app(all_c, atom);
        let ex_c = f.kernel.const_(syn.ex, vec![]);
        let existential = f.kernel.app(ex_c, atom);
        let imp_c = f.kernel.const_(syn.imp, vec![]);
        apply_all(&mut f.kernel, imp_c, &[universal, existential])
    };

    let valuation = {
        let fv = 1_645_020_u64;
        let n = f.kernel.fvar(fv);
        lam_fv(&mut f.kernel, fv, nat_ty, n)
    };
    let true_intro = f.kernel.const_(e.logic.true_intro, vec![]);

    let c = f.kernel.const_(f.p.soundness, vec![]);
    let applied = apply_all(
        &mut f.kernel,
        c,
        &[
            nat_ty, structure, nil, phi, derivation, valuation, true_intro,
        ],
    );
    let got = f
        .kernel
        .infer(applied)
        .expect("soundness must apply to the example derivation");

    let want = {
        let sat_c = f.kernel.const_(f.p.calculus.semantics.sat, vec![]);
        apply_all(&mut f.kernel, sat_c, &[nat_ty, structure, phi, valuation])
    };
    assert!(
        f.kernel.def_eq(got, want),
        "soundness at the example derivation: got {}, want {}",
        f.kernel.render_lean(got),
        f.kernel.render_lean(want)
    );
}

/// `FO.ctxSat_shift` instantiates at the empty context and at a one-entry one,
/// which is the pair of cases its `Context.rec` splits on. A lemma whose
/// `cons` case were unusable would still admit as a whole.
#[test]
fn ctx_sat_shift_instantiates_at_nil_and_at_a_cons() {
    let mut f = Fixture::new();
    let e = f.env();
    let nat_ty = f.nat_ty();
    let structure = f.nat_structure();
    let syn = f.p.calculus.semantics.syntax.names(&mut f.kernel);

    let valuation = {
        let fv = 1_645_030_u64;
        let n = f.kernel.fvar(fv);
        lam_fv(&mut f.kernel, fv, nat_ty, n)
    };
    let witness = f.kernel.const_(syn.nat_zero, vec![]);

    let nil = f.kernel.const_(e.calc.nil, vec![]);
    let true_intro = f.kernel.const_(e.logic.true_intro, vec![]);
    let c = f.kernel.const_(f.p.ctx_sat_shift, vec![]);
    let at_nil = apply_all(
        &mut f.kernel,
        c,
        &[nat_ty, structure, nil, valuation, witness, true_intro],
    );
    f.kernel
        .infer(at_nil)
        .expect("ctxSat_shift must instantiate at the empty context");

    // A one-entry context whose entry is a closed atom, so `ctxSat` there is
    // `And (sat a v) True` and the hypothesis can be built by hand.
    let atom = {
        let zero = f.kernel.const_(syn.nat_zero, vec![]);
        let f0 = f.kernel.const_(syn.f0, vec![]);
        let constant = f.kernel.app(f0, zero);
        let one = {
            let z = f.kernel.const_(syn.nat_zero, vec![]);
            let succ = f.kernel.const_(syn.nat_succ, vec![]);
            f.kernel.app(succ, z)
        };
        let rel2 = f.kernel.const_(syn.rel2, vec![]);
        apply_all(&mut f.kernel, rel2, &[one, constant, constant])
    };
    let g = cons_app(&mut f.kernel, &e.calc, atom, nil);

    // The hypothesis is BOUND rather than supplied, so the term stays closed and
    // `infer` has no free variable to choke on. Its type is built at the
    // CONCRETE carrier and structure -- `ctx_sat_of` would use `SoundEnv`'s
    // ambient `M`/`S` free variables, which are bound inside the declaration
    // but unbound here, and `infer` then reports `UnboundFVar` (measured
    // 2026-09-05 on the first run of this file).
    let h_id = 1_645_031_u64;
    let h = f.kernel.fvar(h_id);
    let hyp_ty = {
        let c = f.kernel.const_(f.p.calculus.ctx_sat, vec![]);
        apply_all(&mut f.kernel, c, &[nat_ty, structure, g, valuation])
    };
    let c = f.kernel.const_(f.p.ctx_sat_shift, vec![]);
    let applied = apply_all(
        &mut f.kernel,
        c,
        &[nat_ty, structure, g, valuation, witness, h],
    );
    let at_cons = lam_fv(&mut f.kernel, h_id, hyp_ty, applied);
    f.kernel
        .infer(at_cons)
        .expect("ctxSat_shift must instantiate at a one-entry context");
}
