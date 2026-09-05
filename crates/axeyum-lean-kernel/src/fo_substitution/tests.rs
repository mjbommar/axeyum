//! Tests for `fo_substitution.rs`.
//!
//! Every declaration here is a `Theorem`, so the kernel admitting it *is* the
//! mathematical check — a wrong statement would not have a proof term. What
//! the tests below add is the other two halves the workspace requires:
//!
//! 1. **axiom-freedom**, asserted after `Environment::contains` (an undeclared
//!    name also reports an empty footprint), and
//! 2. **that the statement is the one claimed** — each theorem's inferred type
//!    is rebuilt here from the constructors and compared, so a lemma that
//!    landed at a weaker-but-still-provable statement fails.
//!
//! Point 2 matters most for `FO.sat_shift` and `FO.sat_inst`, whose proof
//! terms are single applications: a mis-stated corollary would still admit.

use super::*;
use crate::Kernel;

struct Fixture {
    kernel: Kernel,
    p: FoSubstitutionPrelude,
}

impl Fixture {
    fn new() -> Self {
        let mut kernel = Kernel::new();
        let p =
            build_fo_substitution_prelude(&mut kernel).expect("FO substitution prelude must build");
        Self { kernel, p }
    }

    fn env(&mut self) -> Env {
        let sem = self.p.semantics;
        Env::new(&mut self.kernel, &sem)
    }
}

/// Every lemma is declared and axiom-free.
#[test]
fn every_substitution_lemma_is_declared_and_axiom_free() {
    let f = Fixture::new();
    let p = f.p;
    let kernel = f.kernel;
    for (name, label) in [
        (p.val_cons_congr, "FO.Val.cons_congr"),
        (p.eval_congr, "FO.Term.eval_congr"),
        (p.eval_subst, "FO.Term.eval_subst"),
        (p.sat_congr, "FO.sat_congr"),
        (p.sat_subst, "FO.sat_subst"),
        (p.sat_shift, "FO.sat_shift"),
        (p.sat_inst, "FO.sat_inst"),
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

/// `FO.sat_subst`'s inferred type is exactly the substitution lemma, rebuilt
/// here from `FO.sat`, `FO.Formula.subst` and `FO.Term.eval` rather than read
/// off the declaration.
#[test]
fn sat_subst_states_the_substitution_lemma() {
    let mut f = Fixture::new();
    let e = f.env();
    let syntax = f.p.semantics.syntax;

    let p_id = 1_641_001_u64;
    let s_id = 1_641_002_u64;
    let w_id = 1_641_003_u64;
    let p = f.kernel.fvar(p_id);
    let s = f.kernel.fvar(s_id);
    let w = f.kernel.fvar(w_id);

    let substituted = {
        let c = f.kernel.const_(syntax.formula_subst, vec![]);
        apply_all(&mut f.kernel, c, &[p, s])
    };
    let lhs = sat_of(&mut f.kernel, &e, substituted, w);
    let composed = compose(&mut f.kernel, &e, s, w, 1_641_004_u64);
    let rhs = sat_of(&mut f.kernel, &e, p, composed);
    let concl = iff_ty(&mut f.kernel, e.logic, lhs, rhs);
    let want = {
        let inner = pis(
            &mut f.kernel,
            &[(p_id, e.syn.formula_ty), (s_id, e.sub_ty), (w_id, e.val_ty)],
            concl,
        );
        pis(
            &mut f.kernel,
            &[(e.m_id, e.type_sort), (e.s_id, e.struct_m)],
            inner,
        )
    };

    let c = f.kernel.const_(f.p.sat_subst, vec![]);
    let got = f.kernel.infer(c).expect("must infer");
    assert!(
        f.kernel.def_eq(got, want),
        "FO.sat_subst's type: got {}, want {}",
        f.kernel.render_lean(got),
        f.kernel.render_lean(want)
    );
}

/// `FO.sat_shift`'s inferred type is
/// `Π M S p w a, Iff (sat (Formula.shift p) (Val.cons M a w)) (sat p w)`.
///
/// The right-hand side being `sat p w` — and **not** `sat p` at some shifted
/// valuation — is the whole content of the corollary, and it is what the
/// `fo_soundness.rs` `all_intro`/`ex_elim` cases consume. Rebuilt here rather
/// than trusted.
#[test]
fn sat_shift_states_the_shift_corollary() {
    let mut f = Fixture::new();
    let e = f.env();
    let syntax = f.p.semantics.syntax;

    let p_id = 1_641_011_u64;
    let w_id = 1_641_012_u64;
    let a_id = 1_641_013_u64;
    let p = f.kernel.fvar(p_id);
    let w = f.kernel.fvar(w_id);
    let a = f.kernel.fvar(a_id);

    let shifted = {
        let c = f.kernel.const_(syntax.formula_shift, vec![]);
        f.kernel.app(c, p)
    };
    let extended = vcons(&mut f.kernel, &e, a, w);
    let lhs = sat_of(&mut f.kernel, &e, shifted, extended);
    let rhs = sat_of(&mut f.kernel, &e, p, w);
    let concl = iff_ty(&mut f.kernel, e.logic, lhs, rhs);
    let want = {
        let inner = pis(
            &mut f.kernel,
            &[(p_id, e.syn.formula_ty), (w_id, e.val_ty), (a_id, e.m)],
            concl,
        );
        pis(
            &mut f.kernel,
            &[(e.m_id, e.type_sort), (e.s_id, e.struct_m)],
            inner,
        )
    };

    let c = f.kernel.const_(f.p.sat_shift, vec![]);
    let got = f.kernel.infer(c).expect("must infer");
    assert!(
        f.kernel.def_eq(got, want),
        "FO.sat_shift's type: got {}, want {}",
        f.kernel.render_lean(got),
        f.kernel.render_lean(want)
    );

    // Negative control of the same kind: the corollary is NOT the trivial
    // `Iff (sat (shift p) (cons a w)) (sat p (cons a w))`, which would be the
    // statement of a `shift` that did nothing.
    let trivial = {
        let rhs = sat_of(&mut f.kernel, &e, p, extended);
        let concl = iff_ty(&mut f.kernel, e.logic, lhs, rhs);
        let inner = pis(
            &mut f.kernel,
            &[(p_id, e.syn.formula_ty), (w_id, e.val_ty), (a_id, e.m)],
            concl,
        );
        pis(
            &mut f.kernel,
            &[(e.m_id, e.type_sort), (e.s_id, e.struct_m)],
            inner,
        )
    };
    assert!(
        !f.kernel.def_eq(got, trivial),
        "FO.sat_shift must not be the trivial statement about the extended valuation"
    );
}

/// `FO.sat_inst`'s inferred type is
/// `Π M S p t w, Iff (sat (Formula.subst p (Subst.cons t Subst.id)) w)
/// (sat p (Val.cons M (Term.eval M S t w) w))`.
#[test]
fn sat_inst_states_the_instantiation_corollary() {
    let mut f = Fixture::new();
    let e = f.env();
    let syntax = f.p.semantics.syntax;

    let p_id = 1_641_021_u64;
    let t_id = 1_641_022_u64;
    let w_id = 1_641_023_u64;
    let p = f.kernel.fvar(p_id);
    let t = f.kernel.fvar(t_id);
    let w = f.kernel.fvar(w_id);

    let sigma = {
        let id = f.kernel.const_(syntax.subst_id, vec![]);
        let cons = f.kernel.const_(syntax.subst_cons, vec![]);
        apply_all(&mut f.kernel, cons, &[t, id])
    };
    let substituted = {
        let c = f.kernel.const_(syntax.formula_subst, vec![]);
        apply_all(&mut f.kernel, c, &[p, sigma])
    };
    let lhs = sat_of(&mut f.kernel, &e, substituted, w);
    let t_val = ev(&mut f.kernel, &e, t, w);
    let extended = vcons(&mut f.kernel, &e, t_val, w);
    let rhs = sat_of(&mut f.kernel, &e, p, extended);
    let concl = iff_ty(&mut f.kernel, e.logic, lhs, rhs);
    let want = {
        let inner = pis(
            &mut f.kernel,
            &[
                (p_id, e.syn.formula_ty),
                (t_id, e.syn.term_ty),
                (w_id, e.val_ty),
            ],
            concl,
        );
        pis(
            &mut f.kernel,
            &[(e.m_id, e.type_sort), (e.s_id, e.struct_m)],
            inner,
        )
    };

    let c = f.kernel.const_(f.p.sat_inst, vec![]);
    let got = f.kernel.infer(c).expect("must infer");
    assert!(
        f.kernel.def_eq(got, want),
        "FO.sat_inst's type: got {}, want {}",
        f.kernel.render_lean(got),
        f.kernel.render_lean(want)
    );
}

/// The substitution lemma is not vacuous at a concrete instance: applied at
/// the ℕ structure, the sentence `all (ex (rel2 0 (var 1) (var 0)))` and the
/// identity substitution, `FO.sat_subst`'s instance has exactly the `Iff` the
/// general statement predicts.
///
/// This is the positive control a lemma stated over an *empty* family would
/// fail while still being admitted: `Π (M : Type) …` looks inhabited
/// regardless, so applying it at a real carrier and a real structure is what
/// shows the quantification is usable.
#[test]
fn sat_subst_instantiates_at_the_nat_structure() {
    let mut f = Fixture::new();
    let e = f.env();
    let sem = f.p.semantics;
    let syntax = sem.syntax;
    let syn = syntax.names(&mut f.kernel);

    let nat_ty = f.kernel.const_(syntax.nat.nat, vec![]);
    let structure = f.kernel.const_(sem.nat_structure, vec![]);
    let sentence = crate::fo_semantics::nat_no_greatest_sentence(&mut f.kernel, &syn);
    let id_subst = f.kernel.const_(syntax.subst_id, vec![]);
    let valuation = {
        let fv = 1_641_031_u64;
        let n = f.kernel.fvar(fv);
        lam_fv(&mut f.kernel, fv, nat_ty, n)
    };

    let c = f.kernel.const_(f.p.sat_subst, vec![]);
    let applied = apply_all(
        &mut f.kernel,
        c,
        &[nat_ty, structure, sentence, id_subst, valuation],
    );
    let got = f
        .kernel
        .infer(applied)
        .expect("sat_subst must instantiate at the nat structure");

    // The instance's type, rebuilt: `Iff (sat (subst φ id) v) (sat φ (id ∘ v))`
    // at the CONCRETE carrier, so `Env`'s ambient `M`/`S` are replaced by `Nat`
    // and `FO.natStructure`.
    let sat_at = |f: &mut Fixture, phi: ExprId, v: ExprId| -> ExprId {
        let c = f.kernel.const_(sem.sat, vec![]);
        apply_all(&mut f.kernel, c, &[nat_ty, structure, phi, v])
    };
    let substituted = {
        let c = f.kernel.const_(syntax.formula_subst, vec![]);
        apply_all(&mut f.kernel, c, &[sentence, id_subst])
    };
    let lhs = sat_at(&mut f, substituted, valuation);
    let composed = {
        let fv = 1_641_032_u64;
        let n = f.kernel.fvar(fv);
        let s_n = f.kernel.app(id_subst, n);
        let eval_const = f.kernel.const_(sem.term_eval, vec![]);
        let body = apply_all(
            &mut f.kernel,
            eval_const,
            &[nat_ty, structure, s_n, valuation],
        );
        lam_fv(&mut f.kernel, fv, nat_ty, body)
    };
    let rhs = sat_at(&mut f, sentence, composed);
    let want = iff_ty(&mut f.kernel, e.logic, lhs, rhs);

    assert!(
        f.kernel.def_eq(got, want),
        "sat_subst's nat instance: got {}, want {}",
        f.kernel.render_lean(got),
        f.kernel.render_lean(want)
    );
}
