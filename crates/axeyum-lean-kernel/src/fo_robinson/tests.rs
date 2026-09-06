//! Tests for `fo_robinson.rs`.
//!
//! `FO.natStructureQ` and the seven axiom formulas are `Definition`s, so
//! admission proves nothing about them: `FO.Formula` is `FO.Formula` whatever
//! the body says, and a structure whose `fn2` ignored its symbol index would
//! type-check identically. So the structure is pinned by `def_eq` at concrete,
//! small, DISCRIMINATING arguments — `2 · 3` is `6` and NOT `5`, which is what
//! an `fn2` that fell through to `Nat.add` would give — and each axiom is
//! pinned by the rendered type of the model theorem plus a distinctness
//! control against its neighbours.
//!
//! `FO.Q.natModels`, `FO.Q.consistency` and `FO.Term.subst_numeral` are
//! `Theorem`s, so the trusted gate DID check them; what the tests add is (a)
//! the axiom footprint, (b) the rendered type, so a silently weakened
//! statement is a failure here, and (c) the two structure obstructions the
//! module doc rests on.

use super::*;
use crate::Kernel;

struct Fixture {
    kernel: Kernel,
    p: FoRobinsonPrelude,
    r: Rob,
}

impl Fixture {
    fn new() -> Self {
        let mut kernel = Kernel::new();
        let p = build_fo_robinson_prelude(&mut kernel).expect("FO Robinson prelude must build");
        let syntax = p.roundtrip.decode.numbering.code.syntax;
        let semantics = p.soundness.calculus.semantics;
        let calculus = p.soundness.calculus;
        let syn = syntax.names(&mut kernel);
        let calc = calculus.calc(&mut kernel);
        let nat = syntax.nat;
        let logic = nat.logic;
        let zero_lvl = kernel.level_zero();
        let one = kernel.level_succ(zero_lvl);
        let nat_ty = kernel.const_(nat.nat, vec![]);
        let term_ty = kernel.const_(syntax.term, vec![]);
        let formula_ty = kernel.const_(syntax.formula, vec![]);
        let val_ty = arrow(&mut kernel, nat_ty, nat_ty);
        let subst_ty = arrow(&mut kernel, nat_ty, term_ty);
        let anon = kernel.anon();
        let fo = kernel.name_str(anon, "FO");
        let q_ns = kernel.name_str(fo, "Q");
        let r = Rob {
            syn,
            calc,
            logic,
            nat,
            q_ns,
            nat_ty,
            term_ty,
            formula_ty,
            val_ty,
            subst_ty,
            zero_lvl,
            one,
            numeral: p.roundtrip.term_numeral,
            term_subst: syntax.term_subst,
            structure: semantics.structure,
            sat: semantics.sat,
            ctx_sat: calculus.ctx_sat,
        };
        Self { kernel, p, r }
    }

    fn nat_lit(&mut self, n: u32) -> ExprId {
        let mut e = self.kernel.const_(self.r.nat.zero, vec![]);
        let succ = self.kernel.const_(self.r.nat.succ, vec![]);
        for _ in 0..n {
            e = self.kernel.app(succ, e);
        }
        e
    }

    fn assert_eq_expr(&mut self, got: ExprId, want: ExprId, what: &str) {
        assert!(
            self.kernel.def_eq(got, want),
            "{what}: got {}, want {}",
            self.kernel.render_lean(got),
            self.kernel.render_lean(want)
        );
    }

    fn assert_ne_expr(&mut self, got: ExprId, want: ExprId, what: &str) {
        assert!(
            !self.kernel.def_eq(got, want),
            "{what}: expected these NOT to be definitionally equal, but {} = {}",
            self.kernel.render_lean(got),
            self.kernel.render_lean(want)
        );
    }

    /// An empty footprint is also what a MISSING name returns, so the
    /// membership assertion comes first.
    fn assert_axiom_free(&mut self, name: NameId, label: &str) {
        assert!(
            self.kernel.environment().contains(name),
            "{label} must be declared before its footprint means anything"
        );
        let footprint = self.kernel.axiom_footprint(name);
        assert!(
            footprint.is_empty(),
            "{label} must be axiom-free, but rests on {:?}",
            footprint
                .iter()
                .map(|&id| self.kernel.display_name(id).to_string())
                .collect::<Vec<_>>()
        );
    }

    fn rendered_type(&mut self, name: NameId) -> String {
        let declaration = self
            .kernel
            .environment()
            .get(name)
            .expect("declaration must exist");
        let ty = declaration.ty();
        self.kernel.render_lean(ty)
    }
}

// ============================================================================
// The ℕ structure interprets the Robinson signature, and does so by INDEX.
// ============================================================================

/// `FO.natStructureQ`'s five families, read through the projections, at
/// concrete small arguments. Each row is discriminating: an `fn2` that ignored
/// its index would fail the `·` rows, and one that swapped the two branches
/// would fail the `+` rows.
#[test]
fn nat_structure_q_interprets_the_robinson_symbols() {
    let mut f = Fixture::new();
    let s = f.kernel.const_(f.p.nat_structure_q, vec![]);
    let nat_ty = f.r.nat_ty;
    let semantics = f.p.soundness.calculus.semantics;

    // fn0 0 = 0, fn0 3 = 3.
    for k in [0_u32, 3] {
        let idx = f.nat_lit(k);
        let head = f.kernel.const_(semantics.fn0, vec![]);
        let got = apply_all(&mut f.kernel, head, &[nat_ty, s, idx]);
        let want = f.nat_lit(k);
        f.assert_eq_expr(got, want, &format!("fn0 {k}"));
    }

    // fn1 1 x = Nat.succ x, at x = 2.
    {
        let one = f.nat_lit(1);
        let two = f.nat_lit(2);
        let head = f.kernel.const_(semantics.fn1, vec![]);
        let got = apply_all(&mut f.kernel, head, &[nat_ty, s, one, two]);
        let want = f.nat_lit(3);
        f.assert_eq_expr(got, want, "fn1 1 2 (the successor symbol)");
    }

    // fn2 0 = Nat.add: 2 + 3 = 5, and NOT 6.
    {
        let zero = f.nat_lit(0);
        let two = f.nat_lit(2);
        let three = f.nat_lit(3);
        let head = f.kernel.const_(semantics.fn2, vec![]);
        let got = apply_all(&mut f.kernel, head, &[nat_ty, s, zero, two, three]);
        let want = f.nat_lit(5);
        f.assert_eq_expr(got, want, "fn2 0 2 3 (the addition symbol)");
        let product = f.nat_lit(6);
        f.assert_ne_expr(got, product, "fn2 0 must be addition, not multiplication");
    }

    // fn2 1 = Nat.mul: 2 · 3 = 6, and NOT 5.
    {
        let one = f.nat_lit(1);
        let two = f.nat_lit(2);
        let three = f.nat_lit(3);
        let head = f.kernel.const_(semantics.fn2, vec![]);
        let got = apply_all(&mut f.kernel, head, &[nat_ty, s, one, two, three]);
        let want = f.nat_lit(6);
        f.assert_eq_expr(got, want, "fn2 1 2 3 (the multiplication symbol)");
        let sum = f.nat_lit(5);
        f.assert_ne_expr(got, sum, "fn2 1 must be multiplication, not addition");
    }

    // fn2 2 is still multiplication (every non-zero index is), so the family is
    // a genuine two-way dispatch and not an accident of the literal `1`.
    {
        let two_idx = f.nat_lit(2);
        let two = f.nat_lit(2);
        let three = f.nat_lit(3);
        let head = f.kernel.const_(semantics.fn2, vec![]);
        let got = apply_all(&mut f.kernel, head, &[nat_ty, s, two_idx, two, three]);
        let want = f.nat_lit(6);
        f.assert_eq_expr(got, want, "fn2 2 2 3");
    }
}

/// The measurement the module doc rests on: `FO.natStructure` -- the structure
/// `fo_semantics.rs` builds -- has NO multiplication at any symbol index,
/// which is why this slice needed a new structure rather than a new axiom set
/// over the old one.
///
/// One data point is NOT enough, and the first draft of this test was wrong
/// for exactly that reason: `fn2 k x y` is `x + y + k`, so at `(2, 3)` the
/// index `k = 1` gives `6`, which IS `2 * 3`. Two witness pairs pin it --
/// `(3, 4)` agrees with multiplication only at `k = 5` and `(2, 5)` only at
/// `k = 3` -- so no single index can be multiplication, and the positive
/// control below shows each index really is `x + y + k`.
#[test]
fn the_original_nat_structure_has_no_multiplication_symbol() {
    let mut f = Fixture::new();
    let semantics = f.p.soundness.calculus.semantics;
    let s = f.kernel.const_(semantics.nat_structure, vec![]);
    let nat_ty = f.r.nat_ty;

    let matches_product = |f: &mut Fixture, k: u32, x: u32, y: u32| -> bool {
        let idx = f.nat_lit(k);
        let xe = f.nat_lit(x);
        let ye = f.nat_lit(y);
        let head = f.kernel.const_(semantics.fn2, vec![]);
        let got = apply_all(&mut f.kernel, head, &[nat_ty, s, idx, xe, ye]);
        let product = f.nat_lit(x * y);
        f.kernel.def_eq(got, product)
    };

    for k in 0..8_u32 {
        let first = matches_product(&mut f, k, 3, 4);
        let second = matches_product(&mut f, k, 2, 5);
        assert!(
            !(first && second),
            "FO.natStructure.fn2 {k} agrees with multiplication at BOTH (3,4) \
             and (2,5), so it could be the multiplication symbol"
        );
        // Positive control: the family really is `x + y + k`, so the negative
        // above is measuring a live interpretation and not a stuck term.
        let idx = f.nat_lit(k);
        let three = f.nat_lit(3);
        let four = f.nat_lit(4);
        let head = f.kernel.const_(semantics.fn2, vec![]);
        let got = apply_all(&mut f.kernel, head, &[nat_ty, s, idx, three, four]);
        let want = f.nat_lit(7 + k);
        f.assert_eq_expr(
            got,
            want,
            &format!("FO.natStructure.fn2 {k} 3 4 must be 3 + 4 + {k}"),
        );
    }
}

// ============================================================================
// The axioms are seven DISTINCT formulas, and `FO.Q` conses all seven.
// ============================================================================

#[test]
fn the_seven_axioms_are_pairwise_distinct_formulas() {
    let mut f = Fixture::new();
    let names = [
        ("axSuccNeZero", f.p.ax_succ_ne_zero),
        ("axSuccInj", f.p.ax_succ_inj),
        ("axCases", f.p.ax_cases),
        ("axAddZero", f.p.ax_add_zero),
        ("axAddSucc", f.p.ax_add_succ),
        ("axMulZero", f.p.ax_mul_zero),
        ("axMulSucc", f.p.ax_mul_succ),
    ];
    for (i, (label_i, name_i)) in names.iter().enumerate() {
        for (label_j, name_j) in names.iter().skip(i + 1) {
            let a = f.kernel.const_(*name_i, vec![]);
            let b = f.kernel.const_(*name_j, vec![]);
            f.assert_ne_expr(a, b, &format!("FO.Q.{label_i} vs FO.Q.{label_j}"));
        }
    }
}

/// `FO.Q` is the seven-entry context, in the documented order. Rebuilt here
/// from the axiom names rather than compared against `FO.Q`'s own body, so a
/// dropped or reordered entry is a failure.
#[test]
fn q_is_the_seven_axioms_in_order() {
    let mut f = Fixture::new();
    let q = f.kernel.const_(f.p.q, vec![]);
    let ordered = [
        f.p.ax_succ_ne_zero,
        f.p.ax_succ_inj,
        f.p.ax_cases,
        f.p.ax_add_zero,
        f.p.ax_add_succ,
        f.p.ax_mul_zero,
        f.p.ax_mul_succ,
    ];
    let calc = f.p.soundness.calculus.calc(&mut f.kernel);
    let mut want = f.kernel.const_(calc.nil, vec![]);
    for &name in ordered.iter().rev() {
        let head = f.kernel.const_(name, vec![]);
        want = cons_app(&mut f.kernel, &calc, head, want);
    }
    f.assert_eq_expr(q, want, "FO.Q");

    // Negative control: the same seven with the last two swapped is a
    // DIFFERENT context, so the equality above is not vacuous.
    let mut swapped = f.kernel.const_(calc.nil, vec![]);
    let reordered = [
        f.p.ax_succ_ne_zero,
        f.p.ax_succ_inj,
        f.p.ax_cases,
        f.p.ax_add_zero,
        f.p.ax_add_succ,
        f.p.ax_mul_succ,
        f.p.ax_mul_zero,
    ];
    for &name in reordered.iter().rev() {
        let head = f.kernel.const_(name, vec![]);
        swapped = cons_app(&mut f.kernel, &calc, head, swapped);
    }
    f.assert_ne_expr(q, swapped, "FO.Q with axMulZero/axMulSucc swapped");
}

// ============================================================================
// `FO.Term.subst_numeral` computes, and the rendered types are pinned.
// ============================================================================

/// The lemma's content at concrete numerals: substituting anything into
/// `numeral 3` gives `numeral 3` back. Checked by `def_eq` on the STATEMENT's
/// two sides, which is what makes the theorem non-vacuous at a literal.
#[test]
fn substitution_fixes_a_numeral_at_a_literal() {
    let mut f = Fixture::new();
    // sigma := Subst.cons (var 7) Subst.id — a substitution that genuinely
    // moves index 0, so a `Term.subst` that dropped its argument would still
    // pass, but one that failed to recurse would not.
    let sigma = {
        let idx = f.nat_lit(7);
        let var_head = f.kernel.const_(f.r.syn.var, vec![]);
        let v7 = f.kernel.app(var_head, idx);
        let id = f.kernel.const_(f.r.calc.subst_id, vec![]);
        let cons = f.kernel.const_(f.r.calc.subst_cons, vec![]);
        apply_all(&mut f.kernel, cons, &[v7, id])
    };
    for n in [0_u32, 1, 3] {
        let lit = f.nat_lit(n);
        let head = f.kernel.const_(f.p.roundtrip.term_numeral, vec![]);
        let num = f.kernel.app(head, lit);
        let subst_head = f.kernel.const_(f.r.term_subst, vec![]);
        let got = apply_all(&mut f.kernel, subst_head, &[num, sigma]);
        f.assert_eq_expr(got, num, &format!("Term.subst (numeral {n}) sigma"));
    }
    // Positive control: the same substitution does NOT fix `var 0`, so the
    // rows above are measuring closedness rather than an inert substitution.
    {
        let zero = f.nat_lit(0);
        let var_head = f.kernel.const_(f.r.syn.var, vec![]);
        let v0 = f.kernel.app(var_head, zero);
        let subst_head = f.kernel.const_(f.r.term_subst, vec![]);
        let got = apply_all(&mut f.kernel, subst_head, &[v0, sigma]);
        f.assert_ne_expr(got, v0, "the control substitution must move var 0");
    }
}

#[test]
fn the_rendered_types_are_the_stated_ones() {
    let mut f = Fixture::new();
    let rows = [(
        f.p.nat_models,
        "((x0 : ((x0 : AxNat) -> AxNat)) -> FO.ctxSat AxNat FO.natStructureQ FO.Q x0)",
    )];
    for (name, expected) in rows {
        let got = f.rendered_type(name);
        assert_eq!(
            got,
            expected,
            "rendered type of {}",
            f.kernel.display_name(name)
        );
    }
}

/// `FO.Q.consistency`'s type is `Not (FO.Provable FO.Q FO.Formula.bot)` and
/// nothing weaker, checked against a REBUILT expected type rather than against
/// a rendering, so a change in the pretty printer cannot silence it.
#[test]
fn q_consistency_states_the_underivability_of_bot_from_q() {
    let mut f = Fixture::new();
    let q = f.kernel.const_(f.p.q, vec![]);
    let bot = f.kernel.const_(f.r.calc.bot, vec![]);
    let deriv_ty = {
        let c = f.kernel.const_(f.r.calc.provable, vec![]);
        apply_all(&mut f.kernel, c, &[q, bot])
    };
    let want = {
        let not_const = f.kernel.const_(f.r.logic.not, vec![]);
        f.kernel.app(not_const, deriv_ty)
    };
    let c = f.kernel.const_(f.p.consistency, vec![]);
    let got = f.kernel.infer(c).expect("must infer");
    f.assert_eq_expr(got, want, "FO.Q.consistency's type");

    // Negative control: the same statement over the EMPTY context is a
    // different type, so the equality above is not matching on shape alone.
    let weaker = {
        let nil = f.kernel.const_(f.r.calc.nil, vec![]);
        let bot2 = f.kernel.const_(f.r.calc.bot, vec![]);
        let cc = f.kernel.const_(f.r.calc.provable, vec![]);
        let deriv = apply_all(&mut f.kernel, cc, &[nil, bot2]);
        let not_const = f.kernel.const_(f.r.logic.not, vec![]);
        f.kernel.app(not_const, deriv)
    };
    f.assert_ne_expr(got, weaker, "FO.Q.consistency vs FO.consistency");
}

/// `FO.Term.subst_numeral`'s type is the stated one, rebuilt rather than
/// rendered.
#[test]
fn subst_numeral_states_the_full_substitution_lemma() {
    let mut f = Fixture::new();
    let s_id = 1_651_900_u64;
    let n_id = 1_651_901_u64;
    let sigma = f.kernel.fvar(s_id);
    let n = f.kernel.fvar(n_id);
    let num_head = f.kernel.const_(f.p.roundtrip.term_numeral, vec![]);
    let num = f.kernel.app(num_head, n);
    let subst_head = f.kernel.const_(f.r.term_subst, vec![]);
    let lhs = apply_all(&mut f.kernel, subst_head, &[num, sigma]);
    let logic = f.r.logic;
    let term_ty = f.r.term_ty;
    let body = geq(&mut f.kernel, logic, term_ty, lhs, num);
    let nat_ty = f.r.nat_ty;
    let subst_ty = f.r.subst_ty;
    let inner = pi_fv(&mut f.kernel, n_id, nat_ty, body);
    let want = pi_fv(&mut f.kernel, s_id, subst_ty, inner);

    let c = f.kernel.const_(f.p.subst_numeral, vec![]);
    let got = f.kernel.infer(c).expect("must infer");
    f.assert_eq_expr(got, want, "FO.Term.subst_numeral's type");
}

/// `FO.Q.consistency` really is about `FO.Q` and not about the empty context:
/// the two theorems have different types, and both are present.
#[test]
fn q_consistency_is_not_the_empty_context_consistency() {
    let mut f = Fixture::new();
    let mine = f.rendered_type(f.p.consistency);
    let empty = f.rendered_type(f.p.soundness.consistency);
    assert_ne!(
        mine, empty,
        "FO.Q.consistency must be a statement about FO.Q, not about FO.Context.nil"
    );
    assert!(
        mine.contains("FO.Q"),
        "FO.Q.consistency's type must mention FO.Q, got {mine}"
    );
}

// ============================================================================
// The every-declaration sweep.
// ============================================================================

#[test]
fn every_declaration_of_this_slice_is_axiom_free() {
    let mut f = Fixture::new();
    let p = f.p;
    for (name, label) in [
        (p.nat_structure_q, "FO.natStructureQ"),
        (p.ax_succ_ne_zero, "FO.Q.axSuccNeZero"),
        (p.ax_succ_inj, "FO.Q.axSuccInj"),
        (p.ax_cases, "FO.Q.axCases"),
        (p.ax_add_zero, "FO.Q.axAddZero"),
        (p.ax_add_succ, "FO.Q.axAddSucc"),
        (p.ax_mul_zero, "FO.Q.axMulZero"),
        (p.ax_mul_succ, "FO.Q.axMulSucc"),
        (p.q, "FO.Q"),
        (p.nat_models, "FO.Q.natModels"),
        (p.consistency, "FO.Q.consistency"),
        (p.subst_numeral, "FO.Term.subst_numeral"),
    ] {
        f.assert_axiom_free(name, label);
    }
}

/// The number of declarations `build_fo_robinson_prelude` adds on top of
/// `build_nat_prelude`: the whole `fo_roundtrip` chain (61, pinned in
/// `fo_roundtrip/tests.rs`) plus the `semantics`/`provable`/`soundness` chain
/// plus this slice's twelve. Pinned so drift in EITHER direction is a failure.
const FO_ROBINSON_DECLARATIONS: usize = 125;

/// The every-declaration sweep for the whole package, derived from the
/// environment rather than from a list, with coverage controls drawn from BOTH
/// `fo_*` chains so it cannot pass vacuously and cannot pass if the two chains
/// stopped composing.
#[test]
fn the_whole_robinson_package_is_axiom_free() {
    use std::collections::{BTreeMap, BTreeSet};

    let baseline: BTreeSet<String> = {
        let mut kernel = Kernel::new();
        let _ = crate::build_nat_prelude(&mut kernel).expect("Nat prelude must build");
        kernel
            .environment()
            .iter()
            .map(|(_, declaration)| kernel.display_name(declaration.name()).to_string())
            .collect()
    };

    let mut kernel = Kernel::new();
    let _ = build_fo_robinson_prelude(&mut kernel).expect("FO Robinson prelude must build");
    let added: BTreeMap<String, NameId> = kernel
        .environment()
        .iter()
        .map(|(_, declaration)| {
            let id = declaration.name();
            (kernel.display_name(id).to_string(), id)
        })
        .filter(|(name, _)| !baseline.contains(name))
        .collect();

    for control in [
        // this slice
        "FO.natStructureQ",
        "FO.Q",
        "FO.Q.axMulSucc",
        "FO.Q.natModels",
        "FO.Q.consistency",
        "FO.Term.subst_numeral",
        // the arithmetization chain
        "FO.Term.numeral",
        "FO.Code.diagAux_code",
        "FO.Formula.code_injective",
        // the calculus chain
        "FO.Provable",
        "FO.soundness",
        "FO.consistency",
        "FO.sat_inst",
    ] {
        assert!(
            added.contains_key(control),
            "coverage control: {control} must be IN the set difference, or the \
             sweep below passes vacuously; the difference has {} rows",
            added.len()
        );
    }

    let assuming: Vec<&String> = added
        .iter()
        .filter(|(_, id)| !kernel.axiom_footprint(**id).is_empty())
        .map(|(name, _)| name)
        .collect();
    assert!(
        assuming.is_empty(),
        "these declarations rest on axioms: {assuming:?}"
    );

    assert_eq!(
        added.len(),
        FO_ROBINSON_DECLARATIONS,
        "declaration count drifted; the names are {:?}",
        added.keys().collect::<Vec<_>>()
    );
}
