//! Tests for `fo_order.rs`.
//!
//! The six order axioms are `Definition`s of type `FO.Formula`, so admission
//! proves nothing about their bodies: a formula is a formula whatever it says,
//! and an axiom that confused `<` with `≤` — or swapped the two sides of the
//! relation — would type-check identically. Two things pin them. The ℕ model
//! theorem is a `Theorem`, so `FO.Qle.natModels` FAILS to admit if any axiom
//! is false in ℕ, which is exactly the mutation this file's controls exercise;
//! and each axiom is separated from its neighbours by `def_eq`, so a
//! copy-paste duplicate cannot hide.

use super::*;
use crate::Kernel;
use crate::fo_provable::cons_app;

struct Fixture {
    kernel: Kernel,
    p: FoOrderPrelude,
    q: Qle,
}

impl Fixture {
    fn new() -> Self {
        let mut kernel = Kernel::new();
        let p = build_fo_order_prelude(&mut kernel).expect("FO order prelude must build");
        let semantics = p.robinson.soundness.calculus.semantics;
        let calculus = p.robinson.soundness.calculus;
        let r = Rob::new(&mut kernel, p.robinson.roundtrip, semantics, calculus);
        let q = Qle::new(&mut kernel, r);
        Self { kernel, p, q }
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

    /// The thirteen axiom names in context order, rebuilt from the prelude
    /// rather than from a literal list.
    fn ordered(&self) -> [NameId; 13] {
        [
            self.p.ax_lt_zero,
            self.p.ax_lt_succ_cases,
            self.p.ax_lt_succ_step,
            self.p.ax_lt_self_succ,
            self.p.ax_lt_add_right,
            self.p.ax_lt_dest,
            self.p.robinson.ax_succ_ne_zero,
            self.p.robinson.ax_succ_inj,
            self.p.robinson.ax_cases,
            self.p.robinson.ax_add_zero,
            self.p.robinson.ax_add_succ,
            self.p.robinson.ax_mul_zero,
            self.p.robinson.ax_mul_succ,
        ]
    }
}

// ============================================================================
// The context is the six order axioms in front of `FO.Q`.
// ============================================================================

#[test]
fn qle_is_the_six_order_axioms_in_front_of_q() {
    let mut f = Fixture::new();
    let qle = f.kernel.const_(f.p.qle, vec![]);
    let calc = f.p.robinson.soundness.calculus.calc(&mut f.kernel);

    let ordered = f.ordered();
    let mut want = f.kernel.const_(calc.nil, vec![]);
    for &name in ordered.iter().rev() {
        let head = f.kernel.const_(name, vec![]);
        want = cons_app(&mut f.kernel, &calc, head, want);
    }
    f.assert_eq_expr(qle, want, "FO.Qle");

    // Negative control: the same thirteen with two order axioms swapped is a
    // DIFFERENT context, so the equality above is not vacuous.
    let mut swapped_names = ordered;
    swapped_names.swap(0, 1);
    let mut swapped = f.kernel.const_(calc.nil, vec![]);
    for &name in swapped_names.iter().rev() {
        let head = f.kernel.const_(name, vec![]);
        swapped = cons_app(&mut f.kernel, &calc, head, swapped);
    }
    f.assert_ne_expr(qle, swapped, "FO.Qle with axLtZero/axLtSuccCases swapped");
}

/// The tail after the six order axioms is `FO.Q` itself, which is what lets
/// `FO.Qle.natModels` reuse `FO.Q.natModels` instead of re-proving the seven.
#[test]
fn the_tail_after_the_order_axioms_is_exactly_q() {
    let mut f = Fixture::new();
    let calc = f.p.robinson.soundness.calculus.calc(&mut f.kernel);
    let ordered = f.ordered();

    let mut tail = f.kernel.const_(calc.nil, vec![]);
    for &name in ordered[6..].iter().rev() {
        let head = f.kernel.const_(name, vec![]);
        tail = cons_app(&mut f.kernel, &calc, head, tail);
    }
    let q = f.kernel.const_(f.p.robinson.q, vec![]);
    f.assert_eq_expr(tail, q, "the tail of FO.Qle after six conses");

    // Coverage control: the tail after FIVE conses is NOT FO.Q, so the row
    // above pins the count as well as the contents.
    let mut five = f.kernel.const_(calc.nil, vec![]);
    for &name in ordered[5..].iter().rev() {
        let head = f.kernel.const_(name, vec![]);
        five = cons_app(&mut f.kernel, &calc, head, five);
    }
    f.assert_ne_expr(five, q, "the tail of FO.Qle after five conses");
}

/// Thirteen pairwise-distinct formulas: a copy-paste that duplicated an axiom
/// would leave `FO.Qle` a twelve-axiom theory under a thirteen-cons spelling.
#[test]
fn the_thirteen_axioms_are_pairwise_distinct_formulas() {
    let mut f = Fixture::new();
    let ordered = f.ordered();
    for i in 0..ordered.len() {
        for j in (i + 1)..ordered.len() {
            let a = f.kernel.const_(ordered[i], vec![]);
            let b = f.kernel.const_(ordered[j], vec![]);
            let label = format!(
                "{} vs {}",
                f.kernel.display_name(ordered[i]),
                f.kernel.display_name(ordered[j])
            );
            f.assert_ne_expr(a, b, &label);
        }
    }
    // Coverage control: an axiom IS definitionally equal to itself, so the
    // sweep above is measuring `def_eq` and not a constant `false`.
    let a = f.kernel.const_(ordered[0], vec![]);
    let b = f.kernel.const_(ordered[0], vec![]);
    f.assert_eq_expr(a, b, "axLtZero against itself");
}

// ============================================================================
// The axiom bodies say what the module docs claim.
// ============================================================================

/// Each order axiom rebuilt from the combinators, checked by `def_eq` against
/// the declared body. A `<` written with its arguments the wrong way round, or
/// an `S` in the wrong position, fails here.
#[test]
fn the_order_axioms_are_the_stated_formulas() {
    let mut f = Fixture::new();

    // O1: all (imp (rel2 0 (var 0) 0) bot)
    {
        let x = f.q.r.tvar(&mut f.kernel, 0);
        let zero = f.q.r.tzero(&mut f.kernel);
        let atom = f.q.f_lt(&mut f.kernel, x, zero);
        let bot = f.q.r.f_bot(&mut f.kernel);
        let body = f.q.r.f_imp(&mut f.kernel, atom, bot);
        let want = f.q.r.f_all(&mut f.kernel, body);
        let got = f.kernel.const_(f.p.ax_lt_zero, vec![]);
        f.assert_eq_expr(got, want, "FO.Qle.axLtZero");

        // Negative control: `0 < x` is a different formula from `x < 0`.
        let x2 = f.q.r.tvar(&mut f.kernel, 0);
        let zero2 = f.q.r.tzero(&mut f.kernel);
        let flipped_atom = f.q.f_lt(&mut f.kernel, zero2, x2);
        let bot2 = f.q.r.f_bot(&mut f.kernel);
        let flipped_body = f.q.r.f_imp(&mut f.kernel, flipped_atom, bot2);
        let flipped = f.q.r.f_all(&mut f.kernel, flipped_body);
        f.assert_ne_expr(got, flipped, "FO.Qle.axLtZero with `<` reversed");
    }

    // O4: all (rel2 0 (var 0) (S (var 0)))
    {
        let x = f.q.r.tvar(&mut f.kernel, 0);
        let x2 = f.q.r.tvar(&mut f.kernel, 0);
        let sx = f.q.r.tsucc(&mut f.kernel, x2);
        let body = f.q.f_lt(&mut f.kernel, x, sx);
        let want = f.q.r.f_all(&mut f.kernel, body);
        let got = f.kernel.const_(f.p.ax_lt_self_succ, vec![]);
        f.assert_eq_expr(got, want, "FO.Qle.axLtSelfSucc");
    }

    // O5: all (all (rel2 0 (var 0) (S (var 0 + var 1))))
    {
        let x = f.q.r.tvar(&mut f.kernel, 0);
        let x2 = f.q.r.tvar(&mut f.kernel, 0);
        let y = f.q.r.tvar(&mut f.kernel, 1);
        let sum = f.q.r.tadd(&mut f.kernel, x2, y);
        let ssum = f.q.r.tsucc(&mut f.kernel, sum);
        let body = f.q.f_lt(&mut f.kernel, x, ssum);
        let inner = f.q.r.f_all(&mut f.kernel, body);
        let want = f.q.r.f_all(&mut f.kernel, inner);
        let got = f.kernel.const_(f.p.ax_lt_add_right, vec![]);
        f.assert_eq_expr(got, want, "FO.Qle.axLtAddRight");

        // Negative control: `x < S (y + x)` is a different (and in ℕ still
        // true, so the model theorem would NOT catch it) formula.
        let a = f.q.r.tvar(&mut f.kernel, 0);
        let b = f.q.r.tvar(&mut f.kernel, 1);
        let c = f.q.r.tvar(&mut f.kernel, 0);
        let other_sum = f.q.r.tadd(&mut f.kernel, b, c);
        let other_ssum = f.q.r.tsucc(&mut f.kernel, other_sum);
        let other_body = f.q.f_lt(&mut f.kernel, a, other_ssum);
        let other_inner = f.q.r.f_all(&mut f.kernel, other_body);
        let other = f.q.r.f_all(&mut f.kernel, other_inner);
        f.assert_ne_expr(got, other, "FO.Qle.axLtAddRight with the sum flipped");
    }
}

/// `<` is `FO.Formula.rel2 0`, and `FO.natStructureQ` interprets that index as
/// `Nat.lt` — the fact the whole slice rests on. Checked through the structure
/// projection at concrete, small, discriminating arguments: `2 < 5` and `5 < 2`
/// are the SAME proposition shape but different propositions, and `rel2 1` is
/// a different relation again, which is why `≤` could not be a second symbol.
#[test]
fn the_order_symbol_is_rel2_zero_and_is_interpreted_as_nat_lt() {
    let mut f = Fixture::new();
    let semantics = f.p.robinson.soundness.calculus.semantics;
    let s = f.kernel.const_(f.p.robinson.nat_structure_q, vec![]);
    let nat_ty = f.q.r.nat_ty;

    let lit = |f: &mut Fixture, n: u32| -> ExprId {
        let mut e = f.kernel.const_(f.q.r.nat.zero, vec![]);
        let succ = f.kernel.const_(f.q.r.nat.succ, vec![]);
        for _ in 0..n {
            e = f.kernel.app(succ, e);
        }
        e
    };

    let two = lit(&mut f, 2);
    let five = lit(&mut f, 5);
    let zero_idx = lit(&mut f, 0);
    let one_idx = lit(&mut f, 1);

    let projection = f.kernel.const_(semantics.rel2, vec![]);
    let got = apply_all(&mut f.kernel, projection, &[nat_ty, s, zero_idx, two, five]);

    let lt = f.kernel.const_(f.q.r.nat.lt, vec![]);
    let want = apply_all(&mut f.kernel, lt, &[two, five]);
    f.assert_eq_expr(got, want, "rel2 0 2 5");

    // Negative control 1: `Nat.lt 5 2` is a different proposition.
    let reversed = apply_all(&mut f.kernel, lt, &[five, two]);
    f.assert_ne_expr(got, reversed, "rel2 0 2 5 against Nat.lt 5 2");

    // Negative control 2: `rel2 1` is `Nat.lt (x + 1) y`, NOT `Nat.le` — the
    // measured obstruction the module docs cite for not adding `≤` as a second
    // symbol.
    let projection2 = f.kernel.const_(semantics.rel2, vec![]);
    let at_one = apply_all(&mut f.kernel, projection2, &[nat_ty, s, one_idx, two, five]);
    f.assert_ne_expr(at_one, got, "rel2 1 2 5 against rel2 0 2 5");
    let le = f.kernel.const_(f.q.r.nat.le, vec![]);
    let le_two_five = apply_all(&mut f.kernel, le, &[two, five]);
    f.assert_ne_expr(at_one, le_two_five, "rel2 1 2 5 against Nat.le 2 5");
}

// ============================================================================
// The rendered types are the stated ones.
// ============================================================================

#[test]
fn the_rendered_types_are_the_stated_ones() {
    let mut f = Fixture::new();
    let rows = [(
        f.p.nat_models,
        "((x0 : ((x0 : AxNat) -> AxNat)) -> FO.ctxSat AxNat FO.natStructureQ FO.Qle x0)",
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

/// `FO.Qle.consistency`'s type is `Not (FO.Provable FO.Qle FO.Formula.bot)` and
/// nothing weaker, checked against a REBUILT expected type rather than against
/// a rendering, so a change in the pretty printer cannot silence it.
#[test]
fn qle_consistency_states_the_underivability_of_bot_from_qle() {
    let mut f = Fixture::new();
    let bot = f.kernel.const_(f.q.r.calc.bot, vec![]);
    let deriv_ty = f.q.prov(&mut f.kernel, bot);
    let want = {
        let not_const = f.kernel.const_(f.q.r.logic.not, vec![]);
        f.kernel.app(not_const, deriv_ty)
    };
    let got = f
        .kernel
        .environment()
        .get(f.p.consistency)
        .expect("FO.Qle.consistency must exist")
        .ty();
    f.assert_eq_expr(got, want, "FO.Qle.consistency");

    // Negative control: the SAME statement at `FO.Q` is a different type, so
    // this theorem is genuinely about the larger theory.
    let q = f.kernel.const_(f.p.robinson.q, vec![]);
    let bot2 = f.kernel.const_(f.q.r.calc.bot, vec![]);
    let at_q = {
        let c = f.kernel.const_(f.q.r.calc.provable, vec![]);
        apply_all(&mut f.kernel, c, &[q, bot2])
    };
    let not_at_q = {
        let not_const = f.kernel.const_(f.q.r.logic.not, vec![]);
        f.kernel.app(not_const, at_q)
    };
    f.assert_ne_expr(got, not_at_q, "FO.Qle.consistency against FO.Q.consistency");
}

// ============================================================================
// The every-declaration sweep.
// ============================================================================

#[test]
fn every_declaration_of_this_slice_is_axiom_free() {
    let mut f = Fixture::new();
    let p = f.p;
    for (name, label) in [
        (p.ax_lt_zero, "FO.Qle.axLtZero"),
        (p.ax_lt_succ_cases, "FO.Qle.axLtSuccCases"),
        (p.ax_lt_succ_step, "FO.Qle.axLtSuccStep"),
        (p.ax_lt_self_succ, "FO.Qle.axLtSelfSucc"),
        (p.ax_lt_add_right, "FO.Qle.axLtAddRight"),
        (p.ax_lt_dest, "FO.Qle.axLtDest"),
        (p.qle, "FO.Qle"),
        (p.nat_models, "FO.Qle.natModels"),
        (p.consistency, "FO.Qle.consistency"),
    ] {
        f.assert_axiom_free(name, label);
    }
}

/// The every-declaration sweep for the whole package, derived from the
/// environment rather than from a list, with the difference taken against the
/// Robinson package so this slice's own additions are what is swept.
#[test]
fn every_declaration_this_slice_adds_is_axiom_free() {
    use std::collections::{BTreeMap, BTreeSet};

    let baseline: BTreeSet<String> = {
        let mut kernel = Kernel::new();
        let _ =
            crate::build_fo_robinson_prelude(&mut kernel).expect("FO Robinson prelude must build");
        kernel
            .environment()
            .iter()
            .map(|(_, declaration)| kernel.display_name(declaration.name()).to_string())
            .collect()
    };

    let mut kernel = Kernel::new();
    let _ = build_fo_order_prelude(&mut kernel).expect("FO order prelude must build");
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
        "FO.Qle",
        "FO.Qle.axLtZero",
        "FO.Qle.axLtDest",
        "FO.Qle.natModels",
        "FO.Qle.consistency",
    ] {
        assert!(
            added.contains_key(control),
            "coverage control: {control} must be IN the set difference, or the \
             sweep below passes vacuously; the difference has {} rows",
            added.len()
        );
    }
    // And nothing from the Robinson package may reappear here, which is what
    // says the two builders compose rather than duplicate.
    assert!(
        !added.contains_key("FO.Q"),
        "FO.Q must come from the Robinson package, not be redeclared here"
    );

    assert_eq!(
        added.len(),
        QLE_DECLARATIONS,
        "declaration count drifted; the added names are {:?}",
        added.keys().collect::<Vec<_>>()
    );

    for (label, &id) in &added {
        let footprint = kernel.axiom_footprint(id);
        assert!(
            footprint.is_empty(),
            "{label} must be axiom-free, but rests on {:?}",
            footprint
                .iter()
                .map(|&a| kernel.display_name(a).to_string())
                .collect::<Vec<_>>()
        );
    }
}

/// The number of declarations `build_fo_order_prelude` adds on top of
/// `build_fo_robinson_prelude`. Pinned so drift in EITHER direction is a
/// failure.
const QLE_DECLARATIONS: usize = 9;
