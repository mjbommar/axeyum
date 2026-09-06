//! **Robinson's Q as an `FO.Context`** (`fo_*.rs`, ADR-1651): the seven
//! Robinson axioms written down over the signature `0, S, +, ·, <`, the ℕ
//! structure that interprets that signature, `ℕ ⊨ Q`, the consistency of Q
//! that soundness then gives for free, and the numeral arithmetic Q proves.
//!
//! ```text
//! FO.natStructureQ : FO.Structure Nat
//! FO.Q.axSuccNeZero, FO.Q.axSuccInj, FO.Q.axCases,
//! FO.Q.axAddZero, FO.Q.axAddSucc, FO.Q.axMulZero, FO.Q.axMulSucc : FO.Formula
//! FO.Q : FO.Context
//! FO.Q.natModels : Π (v : Nat -> Nat), FO.ctxSat Nat FO.natStructureQ FO.Q v
//! FO.Q.consistency : Not (FO.Provable FO.Q FO.Formula.bot)
//! FO.Term.subst_numeral : Π s n, Eq FO.Term (FO.Term.subst (numeral n) s) (numeral n)
//! ```
//!
//! ## The signature, and why `FO.natStructure` could NOT be the model
//!
//! `fo_syntax.rs` gives `Nat`-indexed families of function symbols at arities
//! `0, 1, 2`. This slice fixes the five Robinson symbols inside those families:
//!
//! | symbol | term | interpreted in `FO.natStructureQ` as |
//! | --- | --- | --- |
//! | `0` | `FO.Term.f0 0` | `Nat.zero` |
//! | `S t` | `FO.Term.f1 1 t` | `Nat.succ` |
//! | `a + b` | `FO.Term.f2 0 a b` | `Nat.add` |
//! | `a · b` | `FO.Term.f2 1 a b` | `Nat.mul` |
//! | `a < b` | `FO.Formula.rel2 0 a b` | `Nat.lt` |
//!
//! The `0` and `S` rows are forced, not chosen: `FO.Term.numeral`
//! (`fo_roundtrip.rs`) is `Nat.rec` with base `FO.Term.f0 0` and step
//! `FO.Term.f1 1`, so the numerals of THIS signature are exactly the numerals
//! the arithmetization already codes. Choosing any other pair would have made
//! the eventual bridge to `FO.Code.diagAux_code` a translation rather than an
//! identity.
//!
//! `FO.natStructure` (`fo_semantics.rs`) cannot be the model, and this is a
//! measured obstruction rather than a preference: its binary family is
//! `fn2 k x y := Nat.add (Nat.add x y) k`, i.e. `x + y + k` at **every** index
//! `k`. No index of that family is multiplication, so `·` has no
//! interpretation there and `Q6`/`Q7` are not merely unproved but
//! unsatisfiable-by-construction. `FO.natStructureQ` therefore dispatches on
//! the symbol index,
//!
//! ```text
//! fn2 := fun k x y => Nat.rec.{1} (motive := fun _ => Nat)
//!                       (Nat.add x y) (fun _ _ => Nat.mul x y) k
//! ```
//!
//! so `fn2 0` ι-reduces to `Nat.add` and `fn2 (succ _)` to `Nat.mul`. The
//! other four families are `FO.natStructure`'s verbatim, which is what keeps
//! `fn1 1 = Nat.succ` and `rel2 0 = Nat.lt` definitional.
//!
//! ## Both `fo_*` chains, in one kernel, for the first time
//!
//! `fo_syntax.rs` has two descendant chains — `semantics → provable →
//! soundness` and `code → numbering → decode → roundtrip` — and each `build_*`
//! entry point rebuilds the whole chain beneath it, so calling two of them on
//! one kernel fails at `FO.Term` with `KernelError::DeclarationExists`. This
//! slice needs BOTH (`FO.Provable` from one, `FO.Term.numeral` from the
//! other), so `fo_semantics.rs`, `fo_provable.rs` and `fo_soundness.rs` each
//! gained a `declare_*_over` entry point that takes the already-built
//! dependency, in the shape `fo_substitution.rs` already used. Nothing else
//! about those files changed, and the three `build_*_prelude` functions keep
//! their signatures and their behaviour.
//!
//! ## The seven axioms
//!
//! De Bruijn indices, so `all (all φ)` has the OUTER variable at index `1`:
//!
//! ```text
//! axSuccNeZero := all (imp (eqf (S (var 0)) 0) bot)
//! axSuccInj    := all (all (imp (eqf (S (var 1)) (S (var 0))) (eqf (var 1) (var 0))))
//! axCases      := all (or_ (eqf (var 0) 0) (ex (eqf (var 1) (S (var 0)))))
//! axAddZero    := all (eqf (var 0 + 0) (var 0))
//! axAddSucc    := all (all (eqf (var 1 + S (var 0)) (S (var 1 + var 0))))
//! axMulZero    := all (eqf (var 0 · 0) 0)
//! axMulSucc    := all (all (eqf (var 1 · S (var 0)) (var 1 · var 0 + var 1)))
//! ```
//!
//! `axCases` is stated as the **disjunction** `x = 0 ∨ ∃y. x = S y`, not as
//! the classically equivalent `¬(x = 0) → ∃y. x = S y`. This kernel has no
//! `Classical.em`, so the two are genuinely different formulas here, and the
//! disjunction is the stronger one — it is what ℕ actually satisfies
//! constructively (by `Nat.rec`), and the weaker form is derivable from it.
//! Taking the weaker one would have been a silent weakening of Q.
//!
//! `<` is in the signature and is interpreted, but none of the seven axioms
//! mentions it: that is Robinson's Q as usually presented (Q1–Q7), where the
//! order is a definitional extension rather than a primitive. Nothing in this
//! slice uses `rel2`.
//!
//! ## `ℕ ⊨ Q`, and consistency for free
//!
//! Each of the seven satisfaction obligations is one line, and four of them
//! are `Eq.refl`, because `Nat.add` and `Nat.mul` recurse on their RIGHT
//! argument in this kernel — so `x + 0 = x`, `x + S y = S (x + y)`,
//! `x · 0 = 0` and `x · S y = x · y + x` are the DEFINING equations, i.e.
//! exactly Q4–Q7. `axSuccNeZero` is `Nat.succ_ne_zero`, `axSuccInj` is
//! `Nat.succ_injective`, and `axCases` is a two-case `Nat.rec` that discards
//! its induction hypothesis.
//!
//! `FO.Q.consistency` is then `FO.soundness` at `FO.natStructureQ` with the
//! constant-zero valuation, exactly as `FO.consistency` is at the empty
//! context: a derivation of `⊥` from Q would give `FO.sat _ _ bot _`, which
//! ι-reduces to `False`. The ℕ structure is doing the work — an arbitrary
//! structure would not do, because its carrier could be empty and the argument
//! still needs a valuation `Nat -> M`.
//!
//! ## The one lemma the de Bruijn encoding forces
//!
//! ```text
//! FO.Term.subst_numeral : Π (s : Nat -> FO.Term) (n : Nat),
//!      Eq FO.Term (FO.Term.subst (FO.Term.numeral n) s) (FO.Term.numeral n)
//! ```
//!
//! `FO.Provable.all_elim`'s conclusion is
//! `Formula.subst p (Subst.cons t Subst.id)`, an UNREDUCED application. When
//! `t` is a closed term of literal constructors that reduces away; when `t` is
//! `FO.Term.numeral a` for a **symbolic** `a` it does not, because
//! `FO.Term.numeral` is a `Nat.rec` stuck on `a`. `FO.Term.subst_numeral` is
//! the lemma that unsticks it, and it is a two-case `Nat.rec` whose successor
//! case is `Eq` congruence under `FO.Term.f1 1` (`Term.subst` ι-reduces
//! through every constructor, so only the numeral itself is stuck).
//!
//! ## Numeral arithmetic, and representability of the pairing
//!
//! ```text
//! FO.Q.add_numeral : Π a b, Provable Q (eqf (numeral a + numeral b) (numeral (a+b)))
//! FO.Q.mul_numeral : Π a b, Provable Q (eqf (numeral a · numeral b) (numeral (a·b)))
//! FO.Q.pairGraph   : Term -> Term -> Term -> Formula
//!                    := fun x y z => eqf (z + z) (((x+y)·(x+y) + (x+y)) + (x+x))
//! FO.Q.pairFormula : Formula := pairGraph (var 2) (var 1) (var 0)
//! FO.Q.pair_represented : Π a b,
//!      Provable Q (pairGraph (numeral a) (numeral b) (numeral (FO.Code.pair a b)))
//! ```
//!
//! Both numeral theorems are `Nat.rec` on the SECOND argument, mirroring the
//! recursion in `Nat.add`/`Nat.mul` and in the axioms `axAddSucc`/`axMulSucc`
//! — which is what makes each successor step a single `eqf_subst` (the Leibniz
//! rule) against the induction hypothesis, with no separate object-level
//! congruence or transitivity lemma. `mul_numeral` needs `add_numeral`:
//! `axMulSucc` gives `a · S k = a · k + a`, and rewriting `a · k` to its
//! numeral leaves an object-level SUM rather than a numeral.
//!
//! `FO.Code.pair a b = FO.Code.tri (a + b) + a` and `tri` is a `Nat.rec`, so
//! the pairing is not first-order definable by unfolding it. What makes it
//! definable with no recursion at all is the doubling identity
//! `FO.Code.tri_two : tri n + tri n = n·n + n`, which turns the graph into one
//! polynomial equation — that is `FO.Q.pairGraph`, and
//! `FO.Q.pair_represented` is the POSITIVE half of representability: Q proves
//! the graph at every numeral triple, by evaluating the polynomial side down
//! to a single numeral in five Leibniz steps and transferring the result in a
//! sixth.
//!
//! ### What is NOT landed, and why it is not a matter of effort
//!
//! The uniqueness half — `Q ⊢ ∀z (pairGraph(ā, b̄, z) → z = pair(a,b)‾)` — is
//! open, and the brief anticipated this. **Q has no induction, and none of its
//! seven axioms says anything about a variable in a `∀` position**: from Q4–Q7
//! one can compute with numerals and nothing else, so `Q ⊢ ∀z (z + z = m̄ → z =
//! k̄)` is not derivable. The textbook route adds the ORDER axioms (Q with
//! `<` constrained, i.e. Q⁺) and the numeral case-split
//! `∀x (x < n̄ → x = 0̄ ∨ … ∨ x = (n-1)‾)`, then Σ₁-completeness on top; that is
//! a strictly larger theory than the seven axioms this slice was asked to
//! write down. `fo_robinson/tests.rs` asserts the ABSENCE of any
//! `FO.Q.pair_unique` rather than leaving the gap as prose.
//!
//! What IS available at this strength is *numeralwise* uniqueness — for each
//! numeral `c̄` with `c ≠ pair(a,b)`, `Q ⊢ ¬ pairGraph(ā, b̄, c̄)` — and it
//! needs one further ingredient this slice does not have: the negative twin
//! `Π a b, ¬(a = b) → Provable Q (imp (eqf (numeral a) (numeral b)) bot)`.
//! That derivation lives under an `imp_intro`, i.e. in the context
//! `cons φ FO.Q` rather than in `FO.Q`, and every helper below is written at
//! the fixed context `FO.Q`; generalising them over the context is the sized
//! next step (the `Rob::prov_q`, `q_axiom_derivation`, `all_elim_at`,
//! `cast_derivation` and `leibniz` group — five signatures).

// The mathematical variables in this group are the ones the literature uses --
// `M`/`S` for a structure, `w`/`v` for a valuation, `s` for a substitution,
// `t` for a term, `p`/`q` for formulas, `g` for a context, `n`/`k` for de
// Bruijn indices. Renaming them to satisfy `many_single_char_names` /
// `similar_names` would make every proof term harder to check against the
// semantics it encodes, which is the only thing that matters here. Same
// judgement, same wording, as `fo_soundness.rs`.
#![allow(clippy::many_single_char_names)]
#![allow(clippy::similar_names)]
// `LogicPrelude` and `NatPrelude` are `Copy` structs of `NameId`s threaded by
// value through every combinator, exactly as the rest of this crate does.
#![allow(clippy::large_types_passed_by_value)]
#![allow(clippy::too_many_arguments)]
#![allow(clippy::too_many_lines)]

use crate::build_fo_roundtrip_prelude;
use crate::fo_provable::declare_fo_provable_over;
use crate::fo_provable::{CalcNames, cons_app, provable_app, rule};
use crate::fo_semantics::declare_fo_semantics_over;
use crate::fo_soundness::declare_fo_soundness_over;
use crate::fo_syntax::SyntaxNames;
use crate::fo_syntax::{
    apply_all, arrow, gcongr, geq, grefl, gsymm, gtrans, gtransport, lam_fv, lams, pi_fv, pis,
};
use crate::{
    BinderInfo, Declaration, ExprId, FoProvablePrelude, FoRoundTripPrelude, FoSemanticsPrelude,
    FoSoundnessPrelude, KernelError, LevelId, LogicPrelude, NameId, NatPrelude, ReducibilityHint,
};

/// Names produced by [`build_fo_robinson_prelude`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct FoRobinsonPrelude {
    /// The arithmetization chain (`FO.Term.numeral`, `FO.Code.diagAux_code`).
    pub roundtrip: FoRoundTripPrelude,
    /// The calculus and its soundness, built over the SAME `fo_syntax`.
    pub soundness: FoSoundnessPrelude,

    // --- the model -----------------------------------------------------------
    /// `FO.natStructureQ : FO.Structure Nat` — ℕ with `+` at `f2 0` and `·` at
    /// `f2 1`.
    pub nat_structure_q: NameId,

    // --- the seven axioms ----------------------------------------------------
    /// `FO.Q.axSuccNeZero : FO.Formula` — `∀x, ¬(S x = 0)`.
    pub ax_succ_ne_zero: NameId,
    /// `FO.Q.axSuccInj : FO.Formula` — `∀x∀y, S x = S y → x = y`.
    pub ax_succ_inj: NameId,
    /// `FO.Q.axCases : FO.Formula` — `∀x, x = 0 ∨ ∃y, x = S y`.
    pub ax_cases: NameId,
    /// `FO.Q.axAddZero : FO.Formula` — `∀x, x + 0 = x`.
    pub ax_add_zero: NameId,
    /// `FO.Q.axAddSucc : FO.Formula` — `∀x∀y, x + S y = S (x + y)`.
    pub ax_add_succ: NameId,
    /// `FO.Q.axMulZero : FO.Formula` — `∀x, x · 0 = 0`.
    pub ax_mul_zero: NameId,
    /// `FO.Q.axMulSucc : FO.Formula` — `∀x∀y, x · S y = x · y + x`.
    pub ax_mul_succ: NameId,

    // --- the theory and its model -------------------------------------------
    /// `FO.Q : FO.Context` — the seven axioms, in the order above.
    pub q: NameId,
    /// `FO.Q.natModels : Π v, FO.ctxSat Nat FO.natStructureQ FO.Q v`.
    pub nat_models: NameId,
    /// `FO.Q.consistency : Not (FO.Provable FO.Q FO.Formula.bot)`.
    pub consistency: NameId,

    // --- the substitution lemma numerals need --------------------------------
    /// `FO.Term.subst_numeral` — a numeral is closed, so substitution fixes it.
    pub subst_numeral: NameId,
    /// `FO.Q.add_numeral : Π a b, Provable Q (numeral a + numeral b = numeral (a+b))`.
    pub add_numeral: NameId,
    /// `FO.Q.mul_numeral : Π a b, Provable Q (numeral a · numeral b = numeral (a·b))`.
    pub mul_numeral: NameId,

    // --- representability of the pairing -------------------------------------
    /// `FO.Code.tri_two : Π n, Eq Nat (tri n + tri n) (n · n + n)`.
    pub tri_two: NameId,
    /// `FO.Code.pair_two` — the doubling identity for `FO.Code.pair`.
    pub pair_two: NameId,
    /// `FO.Q.pairGraph : Term -> Term -> Term -> Formula` — the defining
    /// formula `z + z = ((x+y)·(x+y) + (x+y)) + (x+x)`.
    pub pair_graph: NameId,
    /// `FO.Q.pairFormula : FO.Formula` — `pairGraph (var 2) (var 1) (var 0)`.
    pub pair_formula: NameId,
    /// `FO.Q.pair_represented` — Q proves the graph formula at every numeral
    /// triple `(ā, b̄, pair(a,b)‾)`.
    pub pair_represented: NameId,
}

/// The shared names every builder below threads.
struct Rob {
    syn: SyntaxNames,
    calc: CalcNames,
    logic: LogicPrelude,
    nat: NatPrelude,
    /// The `FO.Q` namespace (which is also the context's own name).
    q_ns: NameId,
    nat_ty: ExprId,
    term_ty: ExprId,
    formula_ty: ExprId,
    /// `Nat -> Nat`, the type of a valuation into the ℕ structure.
    val_ty: ExprId,
    /// `Nat -> FO.Term`, the type of a parallel substitution.
    subst_ty: ExprId,
    zero_lvl: LevelId,
    one: LevelId,
    /// `FO.Term.numeral`, from the arithmetization chain.
    numeral: NameId,
    /// `FO.Term.subst`, from `fo_syntax.rs`.
    term_subst: NameId,
    /// `FO.Structure`, `FO.sat` and `FO.ctxSat`.
    structure: NameId,
    sat: NameId,
    ctx_sat: NameId,
    /// `FO.Provable`'s seventeen constructors, re-interned in rule order.
    rules: [NameId; 17],
    /// `FO.Subst.lift` and `FO.Subst.shift`, from `fo_syntax.rs`.
    subst_lift: NameId,
    subst_shift: NameId,
    /// The `FO.Code` namespace and the pairing it owns (`fo_code.rs`).
    code_ns: NameId,
    code_tri: NameId,
    code_pair: NameId,
}

impl Rob {
    /// Re-gather every name this slice's builders share. Interning a name does
    /// not declare it, so this also runs BEFORE this slice's declarations
    /// exist, and `fo_robinson/tests.rs` calls it to rebuild the same view.
    fn new(
        kernel: &mut crate::Kernel,
        roundtrip: FoRoundTripPrelude,
        semantics: FoSemanticsPrelude,
        calculus: FoProvablePrelude,
    ) -> Self {
        let syntax = roundtrip.decode.numbering.code.syntax;
        let syn = syntax.names(kernel);
        let calc = calculus.calc(kernel);
        let nat = syntax.nat;
        let logic = nat.logic;
        let zero_lvl = kernel.level_zero();
        let one = kernel.level_succ(zero_lvl);
        let nat_ty = kernel.const_(nat.nat, vec![]);
        let term_ty = kernel.const_(syntax.term, vec![]);
        let formula_ty = kernel.const_(syntax.formula, vec![]);
        let val_ty = arrow(kernel, nat_ty, nat_ty);
        let subst_ty = arrow(kernel, nat_ty, term_ty);
        let q_ns = kernel.name_str(syn.fo, "Q");
        let code_ns = kernel.name_str(syn.fo, "Code");

        // The rule order is `fo_provable.rs`'s, and the `rule::*` index
        // constants used below index INTO this array, so the two must agree.
        let rule_names: [&str; 17] = [
            "ax_head",
            "weaken",
            "and_intro",
            "and_elim1",
            "and_elim2",
            "or_intro1",
            "or_intro2",
            "or_elim",
            "imp_intro",
            "imp_elim",
            "bot_elim",
            "all_intro",
            "all_elim",
            "ex_intro",
            "ex_elim",
            "eqf_refl",
            "eqf_subst",
        ];
        let mut rules = [calculus.provable; 17];
        for (slot, label) in rules.iter_mut().zip(rule_names) {
            *slot = kernel.name_str(calculus.provable, label);
        }

        Self {
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
            numeral: roundtrip.term_numeral,
            term_subst: syntax.term_subst,
            structure: semantics.structure,
            sat: semantics.sat,
            ctx_sat: calculus.ctx_sat,
            rules,
            subst_lift: syntax.subst_lift,
            subst_shift: syntax.subst_shift,
            code_ns,
            code_tri: roundtrip.decode.numbering.code.tri,
            code_pair: roundtrip.decode.numbering.code.pair,
        }
    }
}

/// A monotone supply of free-variable ids, disjoint from every other `fo_*`
/// block (ADR-1651 owns the `1_651_xxx` range).
struct Fv(u64);

impl Fv {
    fn next(&mut self) -> u64 {
        self.0 += 1;
        self.0
    }
}

// ============================================================================
// Small combinators over the Robinson signature.
// ============================================================================

impl Rob {
    /// The unary `Nat` literal `Nat.succ^n Nat.zero`. Only ever called at `0`
    /// and `1` — the two symbol indices this signature uses.
    fn nat_lit(&self, kernel: &mut crate::Kernel, n: u32) -> ExprId {
        let mut e = kernel.const_(self.nat.zero, vec![]);
        let succ = kernel.const_(self.nat.succ, vec![]);
        for _ in 0..n {
            e = kernel.app(succ, e);
        }
        e
    }

    /// `FO.Term.var i` at a literal de Bruijn index.
    fn tvar(&self, kernel: &mut crate::Kernel, i: u32) -> ExprId {
        let idx = self.nat_lit(kernel, i);
        let head = kernel.const_(self.syn.var, vec![]);
        kernel.app(head, idx)
    }

    /// `0`, i.e. `FO.Term.f0 0`.
    fn tzero(&self, kernel: &mut crate::Kernel) -> ExprId {
        let idx = self.nat_lit(kernel, 0);
        let head = kernel.const_(self.syn.f0, vec![]);
        kernel.app(head, idx)
    }

    /// `S t`, i.e. `FO.Term.f1 1 t`.
    fn tsucc(&self, kernel: &mut crate::Kernel, t: ExprId) -> ExprId {
        let idx = self.nat_lit(kernel, 1);
        let head = kernel.const_(self.syn.f1, vec![]);
        apply_all(kernel, head, &[idx, t])
    }

    /// `a + b`, i.e. `FO.Term.f2 0 a b`.
    fn tadd(&self, kernel: &mut crate::Kernel, a: ExprId, b: ExprId) -> ExprId {
        let idx = self.nat_lit(kernel, 0);
        let head = kernel.const_(self.syn.f2, vec![]);
        apply_all(kernel, head, &[idx, a, b])
    }

    /// `a · b`, i.e. `FO.Term.f2 1 a b`.
    fn tmul(&self, kernel: &mut crate::Kernel, a: ExprId, b: ExprId) -> ExprId {
        let idx = self.nat_lit(kernel, 1);
        let head = kernel.const_(self.syn.f2, vec![]);
        apply_all(kernel, head, &[idx, a, b])
    }

    /// `FO.Term.numeral n` at a `Nat`-valued expression `n`.
    fn tnum(&self, kernel: &mut crate::Kernel, n: ExprId) -> ExprId {
        let head = kernel.const_(self.numeral, vec![]);
        kernel.app(head, n)
    }

    fn f_eqf(&self, kernel: &mut crate::Kernel, a: ExprId, b: ExprId) -> ExprId {
        let head = kernel.const_(self.syn.eqf, vec![]);
        apply_all(kernel, head, &[a, b])
    }

    fn f_imp(&self, kernel: &mut crate::Kernel, a: ExprId, b: ExprId) -> ExprId {
        let head = kernel.const_(self.syn.imp, vec![]);
        apply_all(kernel, head, &[a, b])
    }

    fn f_or(&self, kernel: &mut crate::Kernel, a: ExprId, b: ExprId) -> ExprId {
        let head = kernel.const_(self.syn.or_, vec![]);
        apply_all(kernel, head, &[a, b])
    }

    fn f_bot(&self, kernel: &mut crate::Kernel) -> ExprId {
        kernel.const_(self.syn.bot, vec![])
    }

    fn f_all(&self, kernel: &mut crate::Kernel, body: ExprId) -> ExprId {
        let head = kernel.const_(self.syn.all, vec![]);
        kernel.app(head, body)
    }

    fn f_ex(&self, kernel: &mut crate::Kernel, body: ExprId) -> ExprId {
        let head = kernel.const_(self.syn.ex, vec![]);
        kernel.app(head, body)
    }

    /// `Nat.add a b`.
    fn nadd(&self, kernel: &mut crate::Kernel, a: ExprId, b: ExprId) -> ExprId {
        let head = kernel.const_(self.nat.add, vec![]);
        apply_all(kernel, head, &[a, b])
    }

    /// `Nat.mul a b`.
    fn nmul(&self, kernel: &mut crate::Kernel, a: ExprId, b: ExprId) -> ExprId {
        let head = kernel.const_(self.nat.mul, vec![]);
        apply_all(kernel, head, &[a, b])
    }

    /// `Nat.succ n`.
    fn nsucc(&self, kernel: &mut crate::Kernel, n: ExprId) -> ExprId {
        let head = kernel.const_(self.nat.succ, vec![]);
        kernel.app(head, n)
    }

    /// `Eq Nat a b`.
    fn neq(&self, kernel: &mut crate::Kernel, a: ExprId, b: ExprId) -> ExprId {
        let ty = self.nat_ty;
        geq(kernel, self.logic, ty, a, b)
    }

    /// `Eq FO.Term a b`.
    fn teq(&self, kernel: &mut crate::Kernel, a: ExprId, b: ExprId) -> ExprId {
        let ty = self.term_ty;
        geq(kernel, self.logic, ty, a, b)
    }

    /// `FO.Term.subst t s`.
    fn tsubst(&self, kernel: &mut crate::Kernel, t: ExprId, s: ExprId) -> ExprId {
        let head = kernel.const_(self.term_subst, vec![]);
        apply_all(kernel, head, &[t, s])
    }

    /// `FO.sat Nat S p v`.
    fn sat_of(&self, kernel: &mut crate::Kernel, s: ExprId, p: ExprId, v: ExprId) -> ExprId {
        let head = kernel.const_(self.sat, vec![]);
        let nat_ty = self.nat_ty;
        apply_all(kernel, head, &[nat_ty, s, p, v])
    }

    /// `FO.ctxSat Nat S g v`.
    fn ctx_sat_of(&self, kernel: &mut crate::Kernel, s: ExprId, g: ExprId, v: ExprId) -> ExprId {
        let head = kernel.const_(self.ctx_sat, vec![]);
        let nat_ty = self.nat_ty;
        apply_all(kernel, head, &[nat_ty, s, g, v])
    }

    /// `FO.Subst.cons t FO.Subst.id`, the de Bruijn spelling of `[t/x]`.
    fn inst_subst(&self, kernel: &mut crate::Kernel, t: ExprId) -> ExprId {
        let id = kernel.const_(self.calc.subst_id, vec![]);
        let cons = kernel.const_(self.calc.subst_cons, vec![]);
        apply_all(kernel, cons, &[t, id])
    }

    /// `FO.Subst.shift`.
    fn shift_subst(&self, kernel: &mut crate::Kernel) -> ExprId {
        kernel.const_(self.subst_shift, vec![])
    }

    /// `FO.Subst.lift sigma`.
    fn lift_subst(&self, kernel: &mut crate::Kernel, sigma: ExprId) -> ExprId {
        let head = kernel.const_(self.subst_lift, vec![]);
        kernel.app(head, sigma)
    }

    /// `FO.Formula.subst p sigma`.
    fn f_subst(&self, kernel: &mut crate::Kernel, p: ExprId, sigma: ExprId) -> ExprId {
        let head = kernel.const_(self.calc.formula_subst, vec![]);
        apply_all(kernel, head, &[p, sigma])
    }

    /// `FO.Provable FO.Q p`.
    fn prov_q(&self, kernel: &mut crate::Kernel, p: ExprId) -> ExprId {
        let q = kernel.const_(self.q_ns, vec![]);
        provable_app(kernel, &self.calc, q, p)
    }

    /// `FO.Term.subst_numeral sigma n`.
    fn subst_numeral_at(
        &self,
        kernel: &mut crate::Kernel,
        subst_numeral: NameId,
        sigma: ExprId,
        n: ExprId,
    ) -> ExprId {
        let head = kernel.const_(subst_numeral, vec![]);
        apply_all(kernel, head, &[sigma, n])
    }
}

// ============================================================================
// The build entry point.
// ============================================================================

/// Build Robinson's Q as an `FO.Context`, its ℕ model, and its consistency.
///
/// This is the first builder that puts BOTH `fo_*` chains in one kernel: the
/// arithmetization (`fo_code` → `fo_roundtrip`, which owns `FO.Term.numeral`)
/// and the calculus (`fo_semantics` → `fo_soundness`). It enters the second
/// chain through the `declare_*_over` entry points so `fo_syntax` is built
/// exactly once.
///
/// # Errors
///
/// Returns the [`KernelError`] from any of the underlying trusted gates if a
/// declaration fails to admit.
pub fn build_fo_robinson_prelude(
    kernel: &mut crate::Kernel,
) -> Result<FoRobinsonPrelude, KernelError> {
    let roundtrip = build_fo_roundtrip_prelude(kernel)?;
    let syntax = roundtrip.decode.numbering.code.syntax;
    let semantics = declare_fo_semantics_over(kernel, syntax)?;
    let calculus = declare_fo_provable_over(kernel, semantics)?;
    let soundness = declare_fo_soundness_over(kernel, calculus)?;

    let r = Rob::new(kernel, roundtrip, semantics, calculus);
    let mut fv = Fv(1_651_000);

    let nat_structure_q = declare_nat_structure_q(kernel, &r, semantics.structure_mk, &mut fv)?;
    let axioms = declare_axioms(kernel, &r)?;
    let q = declare_q_context(kernel, &r, &axioms)?;
    let nat_models = declare_nat_models(kernel, &r, nat_structure_q, &axioms, q, &mut fv)?;
    let consistency = declare_consistency(
        kernel,
        &r,
        &soundness,
        nat_structure_q,
        q,
        nat_models,
        &mut fv,
    )?;
    let subst_numeral = declare_subst_numeral(kernel, &r, &mut fv)?;
    let add_numeral = declare_add_numeral(kernel, &r, &axioms, subst_numeral, &mut fv)?;
    let mul_numeral =
        declare_mul_numeral(kernel, &r, &axioms, subst_numeral, add_numeral, &mut fv)?;
    let tri_two = declare_tri_two(kernel, &r, &mut fv)?;
    let pair_two = declare_pair_two(kernel, &r, tri_two, &mut fv)?;
    let pair_graph = declare_pair_graph(kernel, &r, &mut fv)?;
    let pair_formula = declare_pair_formula(kernel, &r, pair_graph)?;
    let pair_represented = declare_pair_represented(
        kernel,
        &r,
        subst_numeral,
        add_numeral,
        mul_numeral,
        pair_two,
        pair_graph,
        &mut fv,
    )?;

    Ok(FoRobinsonPrelude {
        roundtrip,
        soundness,
        nat_structure_q,
        ax_succ_ne_zero: axioms.succ_ne_zero,
        ax_succ_inj: axioms.succ_inj,
        ax_cases: axioms.cases,
        ax_add_zero: axioms.add_zero,
        ax_add_succ: axioms.add_succ,
        ax_mul_zero: axioms.mul_zero,
        ax_mul_succ: axioms.mul_succ,
        q,
        nat_models,
        consistency,
        subst_numeral,
        add_numeral,
        mul_numeral,
        tri_two,
        pair_two,
        pair_graph,
        pair_formula,
        pair_represented,
    })
}

/// The seven axiom names, in the order `FO.Q` conses them.
struct Axioms {
    succ_ne_zero: NameId,
    succ_inj: NameId,
    cases: NameId,
    add_zero: NameId,
    add_succ: NameId,
    mul_zero: NameId,
    mul_succ: NameId,
}

impl Axioms {
    /// The seven names in context order, so index `i` is the `i`th `cons`.
    fn ordered(&self) -> [NameId; 7] {
        [
            self.succ_ne_zero,
            self.succ_inj,
            self.cases,
            self.add_zero,
            self.add_succ,
            self.mul_zero,
            self.mul_succ,
        ]
    }
}

// ============================================================================
// The ℕ structure for the Robinson signature.
// ============================================================================

/// `FO.natStructureQ : FO.Structure Nat`.
///
/// Four of the five families are `FO.natStructure`'s verbatim; `fn2` is the
/// one that changes, and it dispatches on the symbol index so that `f2 0` is
/// `Nat.add` and `f2 (succ _)` is `Nat.mul`.
fn declare_nat_structure_q(
    kernel: &mut crate::Kernel,
    r: &Rob,
    structure_mk: NameId,
    fv: &mut Fv,
) -> Result<NameId, KernelError> {
    let nat_ty = r.nat_ty;

    // fn0 := fun k => k
    let i_fn0 = {
        let k_id = fv.next();
        let k = kernel.fvar(k_id);
        lam_fv(kernel, k_id, nat_ty, k)
    };
    // fn1 := fun k x => Nat.add x k -- so `f1 1` is `Nat.succ`, definitionally
    let i_fn1 = {
        let k_id = fv.next();
        let x_id = fv.next();
        let k = kernel.fvar(k_id);
        let x = kernel.fvar(x_id);
        let body = r.nadd(kernel, x, k);
        lams(kernel, &[(k_id, nat_ty), (x_id, nat_ty)], body)
    };
    // fn2 := fun k x y => Nat.rec.{1} (fun _ => Nat) (x + y) (fun _ _ => x * y) k
    let i_fn2 = {
        let k_id = fv.next();
        let x_id = fv.next();
        let y_id = fv.next();
        let k = kernel.fvar(k_id);
        let x = kernel.fvar(x_id);
        let y = kernel.fvar(y_id);
        let motive = {
            let anon = kernel.anon();
            kernel.lam(anon, nat_ty, nat_ty, BinderInfo::Default)
        };
        let base = r.nadd(kernel, x, y);
        let step = {
            let j_id = fv.next();
            let ih_id = fv.next();
            let product = r.nmul(kernel, x, y);
            lams(kernel, &[(j_id, nat_ty), (ih_id, nat_ty)], product)
        };
        let rec = kernel.const_(r.nat.rec, vec![r.one]);
        let applied = apply_all(kernel, rec, &[motive, base, step, k]);
        lams(
            kernel,
            &[(k_id, nat_ty), (x_id, nat_ty), (y_id, nat_ty)],
            applied,
        )
    };
    // rel1 := fun k x => Nat.lt k x
    let i_rel1 = {
        let k_id = fv.next();
        let x_id = fv.next();
        let k = kernel.fvar(k_id);
        let x = kernel.fvar(x_id);
        let lt = kernel.const_(r.nat.lt, vec![]);
        let body = apply_all(kernel, lt, &[k, x]);
        lams(kernel, &[(k_id, nat_ty), (x_id, nat_ty)], body)
    };
    // rel2 := fun k x y => Nat.lt (Nat.add x k) y -- so `rel2 0` is `Nat.lt`
    let i_rel2 = {
        let k_id = fv.next();
        let x_id = fv.next();
        let y_id = fv.next();
        let k = kernel.fvar(k_id);
        let x = kernel.fvar(x_id);
        let y = kernel.fvar(y_id);
        let xk = r.nadd(kernel, x, k);
        let lt = kernel.const_(r.nat.lt, vec![]);
        let body = apply_all(kernel, lt, &[xk, y]);
        lams(
            kernel,
            &[(k_id, nat_ty), (x_id, nat_ty), (y_id, nat_ty)],
            body,
        )
    };

    let mk = kernel.const_(structure_mk, vec![]);
    let value = apply_all(kernel, mk, &[nat_ty, i_fn0, i_fn1, i_fn2, i_rel1, i_rel2]);

    let structure_const = kernel.const_(r.structure, vec![]);
    let ty = kernel.app(structure_const, nat_ty);

    let name = kernel.name_str(r.syn.fo, "natStructureQ");
    kernel.add_declaration(Declaration::Definition {
        name,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(0),
    })?;
    Ok(name)
}

// ============================================================================
// The seven axioms and the context.
// ============================================================================

fn declare_formula(
    kernel: &mut crate::Kernel,
    r: &Rob,
    label: &str,
    value: ExprId,
) -> Result<NameId, KernelError> {
    let name = kernel.name_str(r.q_ns, label);
    let ty = r.formula_ty;
    kernel.add_declaration(Declaration::Definition {
        name,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(0),
    })?;
    Ok(name)
}

/// The seven Robinson axioms, each a closed `FO.Formula`.
fn declare_axioms(kernel: &mut crate::Kernel, r: &Rob) -> Result<Axioms, KernelError> {
    // Q1: all (imp (eqf (S (var 0)) 0) bot)
    let succ_ne_zero = {
        let x = r.tvar(kernel, 0);
        let sx = r.tsucc(kernel, x);
        let zero = r.tzero(kernel);
        let atom = r.f_eqf(kernel, sx, zero);
        let bot = r.f_bot(kernel);
        let body = r.f_imp(kernel, atom, bot);
        let value = r.f_all(kernel, body);
        declare_formula(kernel, r, "axSuccNeZero", value)?
    };
    // Q2: all (all (imp (eqf (S (var 1)) (S (var 0))) (eqf (var 1) (var 0))))
    let succ_inj = {
        let x = r.tvar(kernel, 1);
        let y = r.tvar(kernel, 0);
        let sx = r.tsucc(kernel, x);
        let sy = r.tsucc(kernel, y);
        let hyp = r.f_eqf(kernel, sx, sy);
        let x2 = r.tvar(kernel, 1);
        let y2 = r.tvar(kernel, 0);
        let concl = r.f_eqf(kernel, x2, y2);
        let body = r.f_imp(kernel, hyp, concl);
        let inner = r.f_all(kernel, body);
        let value = r.f_all(kernel, inner);
        declare_formula(kernel, r, "axSuccInj", value)?
    };
    // Q3: all (or_ (eqf (var 0) 0) (ex (eqf (var 1) (S (var 0)))))
    let cases = {
        let x = r.tvar(kernel, 0);
        let zero = r.tzero(kernel);
        let left = r.f_eqf(kernel, x, zero);
        let outer = r.tvar(kernel, 1);
        let inner_var = r.tvar(kernel, 0);
        let s_inner = r.tsucc(kernel, inner_var);
        let atom = r.f_eqf(kernel, outer, s_inner);
        let right = r.f_ex(kernel, atom);
        let body = r.f_or(kernel, left, right);
        let value = r.f_all(kernel, body);
        declare_formula(kernel, r, "axCases", value)?
    };
    // Q4: all (eqf (var 0 + 0) (var 0))
    let add_zero = {
        let x = r.tvar(kernel, 0);
        let zero = r.tzero(kernel);
        let lhs = r.tadd(kernel, x, zero);
        let rhs = r.tvar(kernel, 0);
        let body = r.f_eqf(kernel, lhs, rhs);
        let value = r.f_all(kernel, body);
        declare_formula(kernel, r, "axAddZero", value)?
    };
    // Q5: all (all (eqf (var 1 + S (var 0)) (S (var 1 + var 0))))
    let add_succ = {
        let x = r.tvar(kernel, 1);
        let y = r.tvar(kernel, 0);
        let sy = r.tsucc(kernel, y);
        let lhs = r.tadd(kernel, x, sy);
        let x2 = r.tvar(kernel, 1);
        let y2 = r.tvar(kernel, 0);
        let sum = r.tadd(kernel, x2, y2);
        let rhs = r.tsucc(kernel, sum);
        let body = r.f_eqf(kernel, lhs, rhs);
        let inner = r.f_all(kernel, body);
        let value = r.f_all(kernel, inner);
        declare_formula(kernel, r, "axAddSucc", value)?
    };
    // Q6: all (eqf (var 0 * 0) 0)
    let mul_zero = {
        let x = r.tvar(kernel, 0);
        let zero = r.tzero(kernel);
        let lhs = r.tmul(kernel, x, zero);
        let rhs = r.tzero(kernel);
        let body = r.f_eqf(kernel, lhs, rhs);
        let value = r.f_all(kernel, body);
        declare_formula(kernel, r, "axMulZero", value)?
    };
    // Q7: all (all (eqf (var 1 * S (var 0)) (var 1 * var 0 + var 1)))
    let mul_succ = {
        let x = r.tvar(kernel, 1);
        let y = r.tvar(kernel, 0);
        let sy = r.tsucc(kernel, y);
        let lhs = r.tmul(kernel, x, sy);
        let x2 = r.tvar(kernel, 1);
        let y2 = r.tvar(kernel, 0);
        let product = r.tmul(kernel, x2, y2);
        let x3 = r.tvar(kernel, 1);
        let rhs = r.tadd(kernel, product, x3);
        let body = r.f_eqf(kernel, lhs, rhs);
        let inner = r.f_all(kernel, body);
        let value = r.f_all(kernel, inner);
        declare_formula(kernel, r, "axMulSucc", value)?
    };

    Ok(Axioms {
        succ_ne_zero,
        succ_inj,
        cases,
        add_zero,
        add_succ,
        mul_zero,
        mul_succ,
    })
}

/// The context tail after the first `from` axioms — `FO.Context.nil` at
/// `from = 7`.
fn axiom_tail(kernel: &mut crate::Kernel, r: &Rob, axioms: &Axioms, from: usize) -> ExprId {
    let ordered = axioms.ordered();
    let mut acc = kernel.const_(r.calc.nil, vec![]);
    for &name in ordered[from..].iter().rev() {
        let head = kernel.const_(name, vec![]);
        acc = cons_app(kernel, &r.calc, head, acc);
    }
    acc
}

/// `FO.Q : FO.Context`.
fn declare_q_context(
    kernel: &mut crate::Kernel,
    r: &Rob,
    axioms: &Axioms,
) -> Result<NameId, KernelError> {
    let value = axiom_tail(kernel, r, axioms, 0);
    let ty = r.calc.context_ty;
    kernel.add_declaration(Declaration::Definition {
        name: r.q_ns,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(0),
    })?;
    Ok(r.q_ns)
}

// ============================================================================
// ℕ ⊨ Q, and the consistency of Q.
// ============================================================================

/// `FO.Q.natModels : Π (v : Nat -> Nat), FO.ctxSat Nat FO.natStructureQ FO.Q v`.
fn declare_nat_models(
    kernel: &mut crate::Kernel,
    r: &Rob,
    nat_structure_q: NameId,
    axioms: &Axioms,
    q: NameId,
    fv: &mut Fv,
) -> Result<NameId, KernelError> {
    let s = kernel.const_(nat_structure_q, vec![]);

    let v_id = fv.next();
    let v = kernel.fvar(v_id);

    let q_const = kernel.const_(q, vec![]);
    let goal = r.ctx_sat_of(kernel, s, q_const, v);
    let ty = pi_fv(kernel, v_id, r.val_ty, goal);

    let proofs = [
        model_succ_ne_zero(kernel, r, fv),
        model_succ_inj(kernel, r, fv),
        model_cases(kernel, r, fv),
        model_add_zero(kernel, r, fv),
        model_add_succ(kernel, r, fv),
        model_named_law(kernel, r, r.nat.mul_zero, LawShape::Unary, fv),
        model_named_law(kernel, r, r.nat.mul_succ, LawShape::Binary, fv),
    ];

    let ordered = axioms.ordered();
    let mut acc = kernel.const_(r.logic.true_intro, vec![]);
    for index in (0..7).rev() {
        let head_formula = kernel.const_(ordered[index], vec![]);
        let a = r.sat_of(kernel, s, head_formula, v);
        let tail = axiom_tail(kernel, r, axioms, index + 1);
        let b = r.ctx_sat_of(kernel, s, tail, v);
        let intro = kernel.const_(r.logic.and_intro, vec![]);
        acc = apply_all(kernel, intro, &[a, b, proofs[index], acc]);
    }
    let value = lam_fv(kernel, v_id, r.val_ty, acc);

    let name = kernel.name_str(r.q_ns, "natModels");
    kernel.add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value,
    })?;
    Ok(name)
}

/// Whether a defining law quantifies one or two variables.
#[derive(Clone, Copy)]
enum LawShape {
    Unary,
    Binary,
}

/// Q4 in ℕ: `fun x => Eq.refl Nat x`. The goal `fn2 0 x (fn0 0) = x` ι-reduces
/// to `Nat.add x Nat.zero = x`, and `Nat.add` recurses on its right argument.
fn model_add_zero(kernel: &mut crate::Kernel, r: &Rob, fv: &mut Fv) -> ExprId {
    let nat_ty = r.nat_ty;
    let x_id = fv.next();
    let x = kernel.fvar(x_id);
    let body = grefl(kernel, r.logic, nat_ty, x);
    lam_fv(kernel, x_id, nat_ty, body)
}

/// Q5 in ℕ: `fun x y => Eq.refl Nat (Nat.succ (Nat.add x y))`.
fn model_add_succ(kernel: &mut crate::Kernel, r: &Rob, fv: &mut Fv) -> ExprId {
    let nat_ty = r.nat_ty;
    let x_id = fv.next();
    let y_id = fv.next();
    let x = kernel.fvar(x_id);
    let y = kernel.fvar(y_id);
    let sum = r.nadd(kernel, x, y);
    let target = r.nsucc(kernel, sum);
    let body = grefl(kernel, r.logic, nat_ty, target);
    lams(kernel, &[(x_id, nat_ty), (y_id, nat_ty)], body)
}

/// `fun x => law x` / `fun x y => law x y`, for a `Nat` defining equation that
/// is already a theorem (`Nat.mul_zero`, `Nat.mul_succ`).
fn model_named_law(
    kernel: &mut crate::Kernel,
    r: &Rob,
    law: NameId,
    shape: LawShape,
    fv: &mut Fv,
) -> ExprId {
    let nat_ty = r.nat_ty;
    let head = kernel.const_(law, vec![]);
    match shape {
        LawShape::Unary => {
            let x_id = fv.next();
            let x = kernel.fvar(x_id);
            let body = kernel.app(head, x);
            lam_fv(kernel, x_id, nat_ty, body)
        }
        LawShape::Binary => {
            let x_id = fv.next();
            let y_id = fv.next();
            let x = kernel.fvar(x_id);
            let y = kernel.fvar(y_id);
            let body = apply_all(kernel, head, &[x, y]);
            lams(kernel, &[(x_id, nat_ty), (y_id, nat_ty)], body)
        }
    }
}

/// Q1 in ℕ: `fun x h => Nat.succ_ne_zero x h`. The hypothesis binder is
/// written in the reduced form the goal presents (`Eq Nat (Nat.succ x) 0`).
fn model_succ_ne_zero(kernel: &mut crate::Kernel, r: &Rob, fv: &mut Fv) -> ExprId {
    let nat_ty = r.nat_ty;
    let x_id = fv.next();
    let h_id = fv.next();
    let x = kernel.fvar(x_id);
    let h = kernel.fvar(h_id);
    let sx = r.nsucc(kernel, x);
    let zero = kernel.const_(r.nat.zero, vec![]);
    let hyp_ty = r.neq(kernel, sx, zero);
    let head = kernel.const_(r.nat.succ_ne_zero, vec![]);
    let body = apply_all(kernel, head, &[x, h]);
    let inner = lam_fv(kernel, h_id, hyp_ty, body);
    lam_fv(kernel, x_id, nat_ty, inner)
}

/// Q2 in ℕ: `fun x y h => Nat.succ_injective x y h`.
fn model_succ_inj(kernel: &mut crate::Kernel, r: &Rob, fv: &mut Fv) -> ExprId {
    let nat_ty = r.nat_ty;
    let x_id = fv.next();
    let y_id = fv.next();
    let h_id = fv.next();
    let x = kernel.fvar(x_id);
    let y = kernel.fvar(y_id);
    let h = kernel.fvar(h_id);
    let sx = r.nsucc(kernel, x);
    let sy = r.nsucc(kernel, y);
    let hyp_ty = r.neq(kernel, sx, sy);
    let head = kernel.const_(r.nat.succ_injective, vec![]);
    let body = apply_all(kernel, head, &[x, y, h]);
    let inner = lam_fv(kernel, h_id, hyp_ty, body);
    lams(kernel, &[(x_id, nat_ty), (y_id, nat_ty)], inner)
}

/// Q3 in ℕ: `∀x, x = 0 ∨ ∃y, x = S y`, by a two-case `Nat.rec` that discards
/// its induction hypothesis (this is a CASE ANALYSIS, and `Nat.rec` is how
/// this kernel spells one).
fn model_cases(kernel: &mut crate::Kernel, r: &Rob, fv: &mut Fv) -> ExprId {
    let nat_ty = r.nat_ty;

    let disjunction = |kernel: &mut crate::Kernel, n: ExprId, y_id: u64| -> ExprId {
        let zero = kernel.const_(r.nat.zero, vec![]);
        let left = r.neq(kernel, n, zero);
        let y = kernel.fvar(y_id);
        let sy = r.nsucc(kernel, y);
        let eq = r.neq(kernel, n, sy);
        let predicate = lam_fv(kernel, y_id, nat_ty, eq);
        let exists_head = kernel.const_(r.logic.exists_, vec![r.one]);
        let right = apply_all(kernel, exists_head, &[nat_ty, predicate]);
        let or_head = kernel.const_(r.logic.or, vec![]);
        apply_all(kernel, or_head, &[left, right])
    };
    let sides = |kernel: &mut crate::Kernel, n: ExprId, y_id: u64| -> (ExprId, ExprId, ExprId) {
        let zero = kernel.const_(r.nat.zero, vec![]);
        let left = r.neq(kernel, n, zero);
        let y = kernel.fvar(y_id);
        let sy = r.nsucc(kernel, y);
        let eq = r.neq(kernel, n, sy);
        let predicate = lam_fv(kernel, y_id, nat_ty, eq);
        let exists_head = kernel.const_(r.logic.exists_, vec![r.one]);
        let right = apply_all(kernel, exists_head, &[nat_ty, predicate]);
        (left, right, predicate)
    };

    let motive = {
        let n_id = fv.next();
        let y_id = fv.next();
        let n = kernel.fvar(n_id);
        let body = disjunction(kernel, n, y_id);
        lam_fv(kernel, n_id, nat_ty, body)
    };

    let base = {
        let y_id = fv.next();
        let zero = kernel.const_(r.nat.zero, vec![]);
        let (left, right, _) = sides(kernel, zero, y_id);
        let zero2 = kernel.const_(r.nat.zero, vec![]);
        let refl = grefl(kernel, r.logic, nat_ty, zero2);
        let inl = kernel.const_(r.logic.or_inl, vec![]);
        apply_all(kernel, inl, &[left, right, refl])
    };

    let step = {
        let k_id = fv.next();
        let ih_id = fv.next();
        let y_id = fv.next();
        let ih_y_id = fv.next();
        let k = kernel.fvar(k_id);
        let sk = r.nsucc(kernel, k);
        let (left, right, predicate) = sides(kernel, sk, y_id);
        let refl = grefl(kernel, r.logic, nat_ty, sk);
        let intro = kernel.const_(r.logic.exists_intro, vec![r.one]);
        let witnessed = apply_all(kernel, intro, &[nat_ty, predicate, k, refl]);
        let inr = kernel.const_(r.logic.or_inr, vec![]);
        let body = apply_all(kernel, inr, &[left, right, witnessed]);
        let ih_ty = disjunction(kernel, k, ih_y_id);
        let inner = lam_fv(kernel, ih_id, ih_ty, body);
        lam_fv(kernel, k_id, nat_ty, inner)
    };

    let x_id = fv.next();
    let x = kernel.fvar(x_id);
    let rec = kernel.const_(r.nat.rec, vec![r.zero_lvl]);
    let applied = apply_all(kernel, rec, &[motive, base, step, x]);
    lam_fv(kernel, x_id, nat_ty, applied)
}

/// `FO.Q.consistency : Not (FO.Provable FO.Q FO.Formula.bot)`.
fn declare_consistency(
    kernel: &mut crate::Kernel,
    r: &Rob,
    soundness: &FoSoundnessPrelude,
    nat_structure_q: NameId,
    q: NameId,
    nat_models: NameId,
    fv: &mut Fv,
) -> Result<NameId, KernelError> {
    let nat_ty = r.nat_ty;
    let s = kernel.const_(nat_structure_q, vec![]);
    let q_const = kernel.const_(q, vec![]);
    let bot = r.f_bot(kernel);

    let d_id = fv.next();
    let junk_id = fv.next();
    let d = kernel.fvar(d_id);

    let valuation = {
        let zero = kernel.const_(r.nat.zero, vec![]);
        lam_fv(kernel, junk_id, nat_ty, zero)
    };
    let hypothesis = {
        let head = kernel.const_(nat_models, vec![]);
        kernel.app(head, valuation)
    };

    let head = kernel.const_(soundness.soundness, vec![]);
    let body = apply_all(
        kernel,
        head,
        &[nat_ty, s, q_const, bot, d, valuation, hypothesis],
    );

    let deriv_ty = provable_app(kernel, &r.calc, q_const, bot);
    let value = lam_fv(kernel, d_id, deriv_ty, body);
    let ty = {
        let not_const = kernel.const_(r.logic.not, vec![]);
        kernel.app(not_const, deriv_ty)
    };

    let name = kernel.name_str(r.q_ns, "consistency");
    kernel.add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value,
    })?;
    Ok(name)
}

// ============================================================================
// The substitution lemma numerals force.
// ============================================================================

/// `FO.Term.subst_numeral : Π (s : Nat -> FO.Term) (n : Nat),
///   Eq FO.Term (FO.Term.subst (FO.Term.numeral n) s) (FO.Term.numeral n)`.
///
/// A `Nat.rec` on `n`. The base case is `Eq.refl` (`Term.subst (f0 0) s`
/// ι-reduces to `f0 0`), and the successor case is congruence under
/// `FO.Term.f1 1` applied to the induction hypothesis, because
/// `Term.subst (f1 1 t) s` ι-reduces to `f1 1 (Term.subst t s)`.
fn declare_subst_numeral(
    kernel: &mut crate::Kernel,
    r: &Rob,
    fv: &mut Fv,
) -> Result<NameId, KernelError> {
    let nat_ty = r.nat_ty;
    let subst_ty = r.subst_ty;

    let claim = |kernel: &mut crate::Kernel, n: ExprId, s: ExprId| -> ExprId {
        let num = r.tnum(kernel, n);
        let lhs = r.tsubst(kernel, num, s);
        let rhs = r.tnum(kernel, n);
        r.teq(kernel, lhs, rhs)
    };

    let s_id = fv.next();
    let s = kernel.fvar(s_id);

    let motive = {
        let n_id = fv.next();
        let n = kernel.fvar(n_id);
        let body = claim(kernel, n, s);
        lam_fv(kernel, n_id, nat_ty, body)
    };

    let base = {
        let zero = kernel.const_(r.nat.zero, vec![]);
        let target = r.tnum(kernel, zero);
        grefl(kernel, r.logic, r.term_ty, target)
    };

    let step = {
        let k_id = fv.next();
        let ih_id = fv.next();
        let cong_fv = fv.next();
        let k = kernel.fvar(k_id);
        let ih = kernel.fvar(ih_id);
        let num_k = r.tnum(kernel, k);
        let lhs = r.tsubst(kernel, num_k, s);
        let rhs = r.tnum(kernel, k);
        let term_ty = r.term_ty;
        let congruence = gcongr(
            kernel,
            r.logic,
            term_ty,
            term_ty,
            lhs,
            rhs,
            ih,
            &|kernel, t| r.tsucc(kernel, t),
            cong_fv,
        );
        let ih_ty = claim(kernel, k, s);
        let inner = lam_fv(kernel, ih_id, ih_ty, congruence);
        lam_fv(kernel, k_id, nat_ty, inner)
    };

    let n_id = fv.next();
    let n = kernel.fvar(n_id);
    let rec = kernel.const_(r.nat.rec, vec![r.zero_lvl]);
    let applied = apply_all(kernel, rec, &[motive, base, step, n]);
    let value = {
        let inner = lam_fv(kernel, n_id, nat_ty, applied);
        lam_fv(kernel, s_id, subst_ty, inner)
    };
    let ty = {
        let n_id2 = fv.next();
        let n2 = kernel.fvar(n_id2);
        let body = claim(kernel, n2, s);
        let inner = pi_fv(kernel, n_id2, nat_ty, body);
        pi_fv(kernel, s_id, subst_ty, inner)
    };

    let name = kernel.name_str(r.syn.term, "subst_numeral");
    kernel.add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value,
    })?;
    Ok(name)
}

// ============================================================================
// Object-level plumbing: axiom access, instantiation, and the numeral repair.
// ============================================================================

/// `FO.Provable FO.Q A_i` for the `i`th Robinson axiom: `ax_head` at the `i`th
/// tail, then `weaken` back out through the `i` axioms in front of it.
fn q_axiom_derivation(
    kernel: &mut crate::Kernel,
    r: &Rob,
    axioms: &Axioms,
    index: usize,
) -> ExprId {
    let ordered = axioms.ordered();
    let target = kernel.const_(ordered[index], vec![]);
    let tail = axiom_tail(kernel, r, axioms, index + 1);
    let ax_head = kernel.const_(r.rules[rule::AX_HEAD], vec![]);
    let mut derivation = apply_all(kernel, ax_head, &[tail, target]);
    let mut context = cons_app(kernel, &r.calc, target, tail);
    for step in (0..index).rev() {
        let front = kernel.const_(ordered[step], vec![]);
        let weaken = kernel.const_(r.rules[rule::WEAKEN], vec![]);
        derivation = apply_all(kernel, weaken, &[context, target, front, derivation]);
        context = cons_app(kernel, &r.calc, front, context);
    }
    derivation
}

/// `FO.Provable.all_elim FO.Q p t d` — the instance `p[t]` of a universal.
fn all_elim_at(
    kernel: &mut crate::Kernel,
    r: &Rob,
    p: ExprId,
    t: ExprId,
    derivation: ExprId,
) -> ExprId {
    let q = kernel.const_(r.q_ns, vec![]);
    let head = kernel.const_(r.rules[rule::ALL_ELIM], vec![]);
    apply_all(kernel, head, &[q, p, t, derivation])
}

/// Transport a derivation along an equality of formulas: from `h : Eq Formula
/// from to` and `d : Provable Q from`, produce `Provable Q to`.
fn cast_derivation(
    kernel: &mut crate::Kernel,
    r: &Rob,
    from: ExprId,
    to: ExprId,
    h: ExprId,
    d: ExprId,
    fv: &mut Fv,
) -> ExprId {
    let formula_ty = r.formula_ty;
    let x_id = fv.next();
    let motive = {
        let x = kernel.fvar(x_id);
        let concl = r.prov_q(kernel, x);
        let hyp = geq(kernel, r.logic, formula_ty, from, x);
        let anon = kernel.anon();
        let inner = kernel.lam(anon, hyp, concl, BinderInfo::Default);
        lam_fv(kernel, x_id, formula_ty, inner)
    };
    gtransport(kernel, r.logic, formula_ty, from, motive, d, to, h)
}

/// `Eq FO.Formula (shape froms) (shape tos)`, one `gcongr` per hole, chained by
/// `gtrans`. A hole may occur several times in `shape`; all of its occurrences
/// move together, which is exactly what `Formula.subst` does to them.
fn congr_chain(
    kernel: &mut crate::Kernel,
    r: &Rob,
    froms: &[ExprId],
    tos: &[ExprId],
    proofs: &[ExprId],
    shape: &dyn Fn(&mut crate::Kernel, &[ExprId]) -> ExprId,
    fv: &mut Fv,
) -> ExprId {
    let term_ty = r.term_ty;
    let formula_ty = r.formula_ty;
    let mut current: Vec<ExprId> = froms.to_vec();
    let start = shape(kernel, &current);
    let mut acc = grefl(kernel, r.logic, formula_ty, start);
    let mut acc_end = start;
    for index in 0..froms.len() {
        let fixed = current.clone();
        let step = {
            let hole = |kernel: &mut crate::Kernel, t: ExprId| -> ExprId {
                let mut slots = fixed.clone();
                slots[index] = t;
                shape(kernel, &slots)
            };
            let cong_fv = fv.next();
            gcongr(
                kernel,
                r.logic,
                term_ty,
                formula_ty,
                froms[index],
                tos[index],
                proofs[index],
                &hole,
                cong_fv,
            )
        };
        current[index] = tos[index];
        let next_end = shape(kernel, &current);
        let trans_fv = fv.next();
        acc = gtrans(
            kernel, r.logic, formula_ty, start, acc_end, next_end, acc, step, trans_fv,
        );
        acc_end = next_end;
    }
    acc
}

/// One application of `FO.Provable.eqf_subst` (the Leibniz rule) with the
/// numeral repair on both sides.
///
/// `shape(holes, x)` is the formula `p` with its `i`th literal numeral replaced
/// by `holes[i]` and its single `FO.Term.var 0` replaced by `x`. `p` itself is
/// `shape(numerals, var 0)`; the premise proves `p[s]` and the conclusion is
/// `p[t]`, and each of those is `shape(_, s)` / `shape(_, t)` with every hole
/// wrapped in a stuck `FO.Term.subst`, which is what the two `congr_chain`s
/// below undo.
struct Leibniz<'a> {
    /// The `Nat` arguments of the numerals occurring literally in `p`.
    numerals: &'a [ExprId],
    /// `p` as data: the numerals are `Tm::Num` slots into `numerals` and the
    /// rewritten position is `Tm::Hole`.
    shape: &'a EqShape,
    /// The two sides of the equation being used.
    s: ExprId,
    t: ExprId,
}

/// A term of the Robinson signature written over numeral slots and the single
/// rewritten position, so a formula shape is data rather than a closure. Every
/// occurrence of one slot moves together, which is exactly what
/// `FO.Formula.subst` does to the numerals it cannot reduce past.
#[derive(Clone)]
enum Tm {
    /// `FO.Term.var 0` — the position `FO.Provable.eqf_subst` rewrites.
    Hole,
    /// `FO.Term.numeral n` for the slot's `Nat` argument.
    Num(usize),
    Suc(Box<Tm>),
    Add(Box<Tm>, Box<Tm>),
    Mul(Box<Tm>, Box<Tm>),
}

impl Tm {
    fn build(&self, kernel: &mut crate::Kernel, r: &Rob, slots: &[ExprId], hole: ExprId) -> ExprId {
        match self {
            Self::Hole => hole,
            Self::Num(index) => slots[*index],
            Self::Suc(inner) => {
                let t = inner.build(kernel, r, slots, hole);
                r.tsucc(kernel, t)
            }
            Self::Add(left, right) => {
                let a = left.build(kernel, r, slots, hole);
                let b = right.build(kernel, r, slots, hole);
                r.tadd(kernel, a, b)
            }
            Self::Mul(left, right) => {
                let a = left.build(kernel, r, slots, hole);
                let b = right.build(kernel, r, slots, hole);
                r.tmul(kernel, a, b)
            }
        }
    }
}

/// The formula `eqf lhs rhs`, as data.
struct EqShape {
    lhs: Tm,
    rhs: Tm,
}

impl EqShape {
    fn build(&self, kernel: &mut crate::Kernel, r: &Rob, slots: &[ExprId], hole: ExprId) -> ExprId {
        let a = self.lhs.build(kernel, r, slots, hole);
        let b = self.rhs.build(kernel, r, slots, hole);
        r.f_eqf(kernel, a, b)
    }
}

/// `Tm::Num(index)`, spelled without the boxing noise at the call sites.
fn num(index: usize) -> Tm {
    Tm::Num(index)
}

fn suc(inner: Tm) -> Tm {
    Tm::Suc(Box::new(inner))
}

fn add(left: Tm, right: Tm) -> Tm {
    Tm::Add(Box::new(left), Box::new(right))
}

fn mul(left: Tm, right: Tm) -> Tm {
    Tm::Mul(Box::new(left), Box::new(right))
}

fn leibniz(
    kernel: &mut crate::Kernel,
    r: &Rob,
    subst_numeral: NameId,
    step: &Leibniz<'_>,
    equation: ExprId,
    from_proof: ExprId,
    fv: &mut Fv,
) -> ExprId {
    let formula_ty = r.formula_ty;
    let numeral_terms: Vec<ExprId> = step.numerals.iter().map(|&n| r.tnum(kernel, n)).collect();
    let var0 = r.tvar(kernel, 0);
    let p = step.shape.build(kernel, r, &numeral_terms, var0);

    // --- the `s` side: repair `p[s]` back to the numeral-free form.
    let sigma_s = r.inst_subst(kernel, step.s);
    let froms_s: Vec<ExprId> = numeral_terms
        .iter()
        .map(|&nt| r.tsubst(kernel, nt, sigma_s))
        .collect();
    let proofs_s: Vec<ExprId> = step
        .numerals
        .iter()
        .map(|&n| r.subst_numeral_at(kernel, subst_numeral, sigma_s, n))
        .collect();
    let repaired = {
        let shape_s = |kernel: &mut crate::Kernel, holes: &[ExprId]| {
            step.shape.build(kernel, r, holes, step.s)
        };
        let chain = congr_chain(kernel, r, &froms_s, &numeral_terms, &proofs_s, &shape_s, fv);
        let start = shape_s(kernel, &froms_s);
        let end = shape_s(kernel, &numeral_terms);
        let symm_fv = fv.next();
        let back = gsymm(kernel, r.logic, formula_ty, start, end, chain, symm_fv);
        cast_derivation(kernel, r, end, start, back, from_proof, fv)
    };

    // --- the Leibniz rule itself.
    let q = kernel.const_(r.q_ns, vec![]);
    let eqf_subst = kernel.const_(r.rules[rule::EQF_SUBST], vec![]);
    let derived = apply_all(
        kernel,
        eqf_subst,
        &[q, p, step.s, step.t, equation, repaired],
    );

    // --- the `t` side: repair `p[t]` forward to the numeral-free form.
    let sigma_t = r.inst_subst(kernel, step.t);
    let froms_t: Vec<ExprId> = numeral_terms
        .iter()
        .map(|&nt| r.tsubst(kernel, nt, sigma_t))
        .collect();
    let proofs_t: Vec<ExprId> = step
        .numerals
        .iter()
        .map(|&n| r.subst_numeral_at(kernel, subst_numeral, sigma_t, n))
        .collect();
    let shape_t =
        |kernel: &mut crate::Kernel, holes: &[ExprId]| step.shape.build(kernel, r, holes, step.t);
    let chain = congr_chain(kernel, r, &froms_t, &numeral_terms, &proofs_t, &shape_t, fv);
    let start = shape_t(kernel, &froms_t);
    let end = shape_t(kernel, &numeral_terms);
    cast_derivation(kernel, r, start, end, chain, derived, fv)
}

/// The two-variable axiom instance `A[numeral a][numeral b]`, with the outer
/// variable's numeral repaired.
///
/// The outer instantiation leaves `numeral a` under `FO.Subst.lift`, i.e. under
/// `Term.subst (numeral a) Subst.shift`, and the inner one wraps that again —
/// so the occurrence the goal wants as a bare `numeral a` arrives as a
/// two-deep stuck substitution. That is the one place `FO.Term.subst_numeral`
/// is needed twice.
fn instantiate_binary_axiom(
    kernel: &mut crate::Kernel,
    r: &Rob,
    axioms: &Axioms,
    subst_numeral: NameId,
    axiom_index: usize,
    inner_body: ExprId,
    outer: ExprId,
    outer_nat: ExprId,
    inner: ExprId,
    shape: &dyn Fn(&mut crate::Kernel, ExprId) -> ExprId,
    fv: &mut Fv,
) -> ExprId {
    let term_ty = r.term_ty;
    let formula_ty = r.formula_ty;

    let universal = q_axiom_derivation(kernel, r, axioms, axiom_index);
    let one_binder = r.f_all(kernel, inner_body);
    let outer_instance = all_elim_at(kernel, r, one_binder, outer, universal);
    let sigma_outer = r.inst_subst(kernel, outer);
    let lifted = r.lift_subst(kernel, sigma_outer);
    let under_binder = r.f_subst(kernel, inner_body, lifted);
    let raw = all_elim_at(kernel, r, under_binder, inner, outer_instance);

    // The stuck occurrence of the outer numeral, and its repair.
    let shift = r.shift_subst(kernel);
    let sigma_inner = r.inst_subst(kernel, inner);
    let shifted = r.tsubst(kernel, outer, shift);
    let stuck = r.tsubst(kernel, shifted, sigma_inner);
    let repair = {
        let first = r.subst_numeral_at(kernel, subst_numeral, shift, outer_nat);
        let cong_fv = fv.next();
        let lifted_first = gcongr(
            kernel,
            r.logic,
            term_ty,
            term_ty,
            shifted,
            outer,
            first,
            &|kernel, t| r.tsubst(kernel, t, sigma_inner),
            cong_fv,
        );
        let middle = r.tsubst(kernel, outer, sigma_inner);
        let second = r.subst_numeral_at(kernel, subst_numeral, sigma_inner, outer_nat);
        let trans_fv = fv.next();
        gtrans(
            kernel,
            r.logic,
            term_ty,
            stuck,
            middle,
            outer,
            lifted_first,
            second,
            trans_fv,
        )
    };
    let cong_fv = fv.next();
    let formula_eq = gcongr(
        kernel, r.logic, term_ty, formula_ty, stuck, outer, repair, shape, cong_fv,
    );
    let from = shape(kernel, stuck);
    let to = shape(kernel, outer);
    cast_derivation(kernel, r, from, to, formula_eq, raw, fv)
}

// ============================================================================
// Numeral addition and multiplication in Q.
// ============================================================================

/// `FO.Q.add_numeral : Π (a b : Nat), FO.Provable FO.Q
///   (eqf (numeral a + numeral b) (numeral (Nat.add a b)))`.
///
/// `Nat.rec` on `b`, mirroring the recursion in `Nat.add` and in `axAddSucc`.
/// The base case is `axAddZero` at `numeral a` and needs no repair at all
/// (the axiom body contains no numerals, so `Formula.subst` reduces through
/// it); the successor case is `axAddSucc` at `(numeral a, numeral b)` followed
/// by one Leibniz step against the induction hypothesis.
fn declare_add_numeral(
    kernel: &mut crate::Kernel,
    r: &Rob,
    axioms: &Axioms,
    subst_numeral: NameId,
    fv: &mut Fv,
) -> Result<NameId, KernelError> {
    let nat_ty = r.nat_ty;
    let a_id = fv.next();
    let a = kernel.fvar(a_id);

    let claim = |kernel: &mut crate::Kernel, b: ExprId| -> ExprId {
        let na = r.tnum(kernel, a);
        let nb = r.tnum(kernel, b);
        let lhs = r.tadd(kernel, na, nb);
        let sum = r.nadd(kernel, a, b);
        let rhs = r.tnum(kernel, sum);
        let formula = r.f_eqf(kernel, lhs, rhs);
        r.prov_q(kernel, formula)
    };

    let motive = {
        let b_id = fv.next();
        let b = kernel.fvar(b_id);
        let body = claim(kernel, b);
        lam_fv(kernel, b_id, nat_ty, body)
    };

    let base = {
        let body = {
            let x = r.tvar(kernel, 0);
            let zero = r.tzero(kernel);
            let lhs = r.tadd(kernel, x, zero);
            let rhs = r.tvar(kernel, 0);
            r.f_eqf(kernel, lhs, rhs)
        };
        let universal = q_axiom_derivation(kernel, r, axioms, 3);
        let na = r.tnum(kernel, a);
        all_elim_at(kernel, r, body, na, universal)
    };

    let step = {
        let k_id = fv.next();
        let ih_id = fv.next();
        let k = kernel.fvar(k_id);
        let ih = kernel.fvar(ih_id);
        let na = r.tnum(kernel, a);
        let nk = r.tnum(kernel, k);

        let inner_body = {
            let x = r.tvar(kernel, 1);
            let y = r.tvar(kernel, 0);
            let sy = r.tsucc(kernel, y);
            let lhs = r.tadd(kernel, x, sy);
            let x2 = r.tvar(kernel, 1);
            let y2 = r.tvar(kernel, 0);
            let sum = r.tadd(kernel, x2, y2);
            let rhs = r.tsucc(kernel, sum);
            r.f_eqf(kernel, lhs, rhs)
        };
        // shape(u) := eqf (u + S nk) (S (u + nk))
        let instance_shape = |kernel: &mut crate::Kernel, u: ExprId| -> ExprId {
            let snk = r.tsucc(kernel, nk);
            let lhs = r.tadd(kernel, u, snk);
            let sum = r.tadd(kernel, u, nk);
            let rhs = r.tsucc(kernel, sum);
            r.f_eqf(kernel, lhs, rhs)
        };
        let major = instantiate_binary_axiom(
            kernel,
            r,
            axioms,
            subst_numeral,
            4,
            inner_body,
            na,
            a,
            nk,
            &instance_shape,
            fv,
        );

        let s = r.tadd(kernel, na, nk);
        let t = {
            let sum = r.nadd(kernel, a, k);
            r.tnum(kernel, sum)
        };
        let shape = EqShape {
            lhs: add(num(0), suc(num(1))),
            rhs: suc(Tm::Hole),
        };
        let numerals = [a, k];
        let plan = Leibniz {
            numerals: &numerals,
            shape: &shape,
            s,
            t,
        };
        let body = leibniz(kernel, r, subst_numeral, &plan, ih, major, fv);
        let ih_ty = claim(kernel, k);
        lams(kernel, &[(k_id, nat_ty), (ih_id, ih_ty)], body)
    };

    let b_id = fv.next();
    let b = kernel.fvar(b_id);
    let rec = kernel.const_(r.nat.rec, vec![r.zero_lvl]);
    let applied = apply_all(kernel, rec, &[motive, base, step, b]);
    let value = lams(kernel, &[(a_id, nat_ty), (b_id, nat_ty)], applied);
    let ty = {
        let b2_id = fv.next();
        let b2 = kernel.fvar(b2_id);
        let body = claim(kernel, b2);
        pis(kernel, &[(a_id, nat_ty), (b2_id, nat_ty)], body)
    };

    let name = kernel.name_str(r.q_ns, "add_numeral");
    kernel.add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value,
    })?;
    Ok(name)
}

/// `FO.Q.mul_numeral : Π (a b : Nat), FO.Provable FO.Q
///   (eqf (numeral a · numeral b) (numeral (Nat.mul a b)))`.
///
/// `Nat.rec` on `b` again. The successor case needs TWO Leibniz steps, because
/// `axMulSucc` leaves `a · S k = a · k + a`, and rewriting `a · k` to its
/// numeral gives `numeral (a·k) + numeral a` — an object-level SUM, not yet a
/// numeral. `FO.Q.add_numeral` at `(Nat.mul a k, a)` is what closes it, which
/// is why the multiplicative theorem depends on the additive one.
fn declare_mul_numeral(
    kernel: &mut crate::Kernel,
    r: &Rob,
    axioms: &Axioms,
    subst_numeral: NameId,
    add_numeral: NameId,
    fv: &mut Fv,
) -> Result<NameId, KernelError> {
    let nat_ty = r.nat_ty;
    let a_id = fv.next();
    let a = kernel.fvar(a_id);

    let claim = |kernel: &mut crate::Kernel, b: ExprId| -> ExprId {
        let na = r.tnum(kernel, a);
        let nb = r.tnum(kernel, b);
        let lhs = r.tmul(kernel, na, nb);
        let product = r.nmul(kernel, a, b);
        let rhs = r.tnum(kernel, product);
        let formula = r.f_eqf(kernel, lhs, rhs);
        r.prov_q(kernel, formula)
    };

    let motive = {
        let b_id = fv.next();
        let b = kernel.fvar(b_id);
        let body = claim(kernel, b);
        lam_fv(kernel, b_id, nat_ty, body)
    };

    let base = {
        let body = {
            let x = r.tvar(kernel, 0);
            let zero = r.tzero(kernel);
            let lhs = r.tmul(kernel, x, zero);
            let rhs = r.tzero(kernel);
            r.f_eqf(kernel, lhs, rhs)
        };
        let universal = q_axiom_derivation(kernel, r, axioms, 5);
        let na = r.tnum(kernel, a);
        all_elim_at(kernel, r, body, na, universal)
    };

    let step = {
        let k_id = fv.next();
        let ih_id = fv.next();
        let k = kernel.fvar(k_id);
        let ih = kernel.fvar(ih_id);
        let na = r.tnum(kernel, a);
        let nk = r.tnum(kernel, k);

        let inner_body = {
            let x = r.tvar(kernel, 1);
            let y = r.tvar(kernel, 0);
            let sy = r.tsucc(kernel, y);
            let lhs = r.tmul(kernel, x, sy);
            let x2 = r.tvar(kernel, 1);
            let y2 = r.tvar(kernel, 0);
            let product = r.tmul(kernel, x2, y2);
            let x3 = r.tvar(kernel, 1);
            let rhs = r.tadd(kernel, product, x3);
            r.f_eqf(kernel, lhs, rhs)
        };
        // shape(u) := eqf (u · S nk) (u · nk + u)
        let instance_shape = |kernel: &mut crate::Kernel, u: ExprId| -> ExprId {
            let snk = r.tsucc(kernel, nk);
            let lhs = r.tmul(kernel, u, snk);
            let product = r.tmul(kernel, u, nk);
            let rhs = r.tadd(kernel, product, u);
            r.f_eqf(kernel, lhs, rhs)
        };
        let major = instantiate_binary_axiom(
            kernel,
            r,
            axioms,
            subst_numeral,
            6,
            inner_body,
            na,
            a,
            nk,
            &instance_shape,
            fv,
        );

        let numerals = [a, k];

        // Step one: rewrite `numeral a · numeral k` to `numeral (a · k)`.
        let partial = {
            let s = r.tmul(kernel, na, nk);
            let t = {
                let product = r.nmul(kernel, a, k);
                r.tnum(kernel, product)
            };
            let shape = EqShape {
                lhs: mul(num(0), suc(num(1))),
                rhs: add(Tm::Hole, num(0)),
            };
            let plan = Leibniz {
                numerals: &numerals,
                shape: &shape,
                s,
                t,
            };
            leibniz(kernel, r, subst_numeral, &plan, ih, major, fv)
        };

        // Step two: collapse the object-level sum `numeral (a·k) + numeral a`.
        let body = {
            let product = r.nmul(kernel, a, k);
            let np = r.tnum(kernel, product);
            let s = r.tadd(kernel, np, na);
            let t = {
                let total = r.nadd(kernel, product, a);
                r.tnum(kernel, total)
            };
            let equation = {
                let head = kernel.const_(add_numeral, vec![]);
                apply_all(kernel, head, &[product, a])
            };
            let shape = EqShape {
                lhs: mul(num(0), suc(num(1))),
                rhs: Tm::Hole,
            };
            let plan = Leibniz {
                numerals: &numerals,
                shape: &shape,
                s,
                t,
            };
            leibniz(kernel, r, subst_numeral, &plan, equation, partial, fv)
        };

        let ih_ty = claim(kernel, k);
        lams(kernel, &[(k_id, nat_ty), (ih_id, ih_ty)], body)
    };

    let b_id = fv.next();
    let b = kernel.fvar(b_id);
    let rec = kernel.const_(r.nat.rec, vec![r.zero_lvl]);
    let applied = apply_all(kernel, rec, &[motive, base, step, b]);
    let value = lams(kernel, &[(a_id, nat_ty), (b_id, nat_ty)], applied);
    let ty = {
        let b2_id = fv.next();
        let b2 = kernel.fvar(b2_id);
        let body = claim(kernel, b2);
        pis(kernel, &[(a_id, nat_ty), (b2_id, nat_ty)], body)
    };

    let name = kernel.name_str(r.q_ns, "mul_numeral");
    kernel.add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value,
    })?;
    Ok(name)
}

// ============================================================================
// Representability of `FO.Code.pair` in Q.
// ============================================================================
//
// `FO.Code.pair a b = FO.Code.tri (a + b) + a`, and `tri` is a `Nat.rec`, so
// the pairing is NOT first-order definable by unfolding it. What makes it
// definable without any recursion is the doubling identity
// `tri n + tri n = n · n + n`, which turns the graph of `pair` into a single
// polynomial equation:
//
//     pair a b = c   iff   c + c = ((a+b)·(a+b) + (a+b)) + (a+a)
//
// The right-hand side is a term of the Robinson signature, so
// `FO.Q.pairGraph` is a genuine `FO.Formula` in three free variables, and
// `FO.Q.pair_represented` is the POSITIVE half of representability: Q proves
// the graph at every numeral triple `(ā, b̄, pair(a,b)‾)`.
//
// The other half -- `Q ⊢ ∀z (pairGraph(ā, b̄, z) → z = pair(a,b)‾)` -- is NOT
// landed and is not a matter of effort: Q has no induction and none of its
// seven axioms constrains a variable, so `Q ⊢ ∀z (z + z = m̄ → z = k̄)` is not
// available. The standard route to it adds the order axioms of Q⁺ and the
// `∀x (x < n̄ → x = 0̄ ∨ … ∨ x = (n-1)‾)` machinery, i.e. a strictly larger
// theory than the seven axioms this slice was asked for. See the module docs.

/// `FO.Code.tri_two : Π (n : Nat),
///   Eq Nat (Nat.add (tri n) (tri n)) (Nat.add (Nat.mul n n) n)`.
///
/// `Nat.rec` on `n`. `FO.Code.tri` is `Nat.rec 0 (fun k ih => ih + succ k)`, so
/// `tri 0` and `tri (succ k)` ι-reduce to `0` and `tri k + succ k`; the base
/// case is `Eq.refl` and the successor case is four rewrites:
/// `add_add_add_comm` to pair the two copies, the induction hypothesis,
/// `add_assoc` backwards, and `succ_mul` backwards (`mul (S k) (S k)` already
/// ι-reduces to `mul (S k) k + S k`, so only the inner product needs it).
fn declare_tri_two(
    kernel: &mut crate::Kernel,
    r: &Rob,
    fv: &mut Fv,
) -> Result<NameId, KernelError> {
    let nat_ty = r.nat_ty;
    let tri = |kernel: &mut crate::Kernel, n: ExprId| -> ExprId {
        let head = kernel.const_(r.code_tri, vec![]);
        kernel.app(head, n)
    };
    let claim = |kernel: &mut crate::Kernel, n: ExprId| -> ExprId {
        let t = tri(kernel, n);
        let t2 = tri(kernel, n);
        let lhs = r.nadd(kernel, t, t2);
        let square = r.nmul(kernel, n, n);
        let rhs = r.nadd(kernel, square, n);
        r.neq(kernel, lhs, rhs)
    };

    let motive = {
        let n_id = fv.next();
        let n = kernel.fvar(n_id);
        let body = claim(kernel, n);
        lam_fv(kernel, n_id, nat_ty, body)
    };

    let base = {
        let zero = kernel.const_(r.nat.zero, vec![]);
        grefl(kernel, r.logic, nat_ty, zero)
    };

    let step = {
        let k_id = fv.next();
        let ih_id = fv.next();
        let k = kernel.fvar(k_id);
        let ih = kernel.fvar(ih_id);
        let sk = r.nsucc(kernel, k);
        let tri_k = tri(kernel, k);
        let square = r.nmul(kernel, k, k);
        let square_plus = r.nadd(kernel, square, k);
        let two_sk = r.nadd(kernel, sk, sk);

        // L0 := (tri k + S k) + (tri k + S k)
        let leg = r.nadd(kernel, tri_k, sk);
        let l0 = r.nadd(kernel, leg, leg);
        // L1 := (tri k + tri k) + (S k + S k)
        let doubled = r.nadd(kernel, tri_k, tri_k);
        let l1 = r.nadd(kernel, doubled, two_sk);
        let h1 = {
            let head = kernel.const_(r.nat.add_add_add_comm, vec![]);
            apply_all(kernel, head, &[tri_k, sk, tri_k, sk])
        };

        // L2 := (k·k + k) + (S k + S k), by the induction hypothesis.
        let l2 = r.nadd(kernel, square_plus, two_sk);
        let cong_fv = fv.next();
        let h2 = gcongr(
            kernel,
            r.logic,
            nat_ty,
            nat_ty,
            doubled,
            square_plus,
            ih,
            &|kernel, u| r.nadd(kernel, u, two_sk),
            cong_fv,
        );

        // L3 := ((k·k + k) + S k) + S k, by `add_assoc` backwards.
        let inner_sum = r.nadd(kernel, square_plus, sk);
        let l3 = r.nadd(kernel, inner_sum, sk);
        let h3 = {
            let head = kernel.const_(r.nat.add_assoc, vec![]);
            let forward = apply_all(kernel, head, &[square_plus, sk, sk]);
            let symm_fv = fv.next();
            gsymm(kernel, r.logic, nat_ty, l3, l2, forward, symm_fv)
        };

        // L4 := ((S k · k) + S k) + S k, by `succ_mul` backwards. This is
        // definitionally `S k · S k + S k`, the goal's right-hand side.
        let succ_product = r.nmul(kernel, sk, k);
        let l4 = {
            let inner = r.nadd(kernel, succ_product, sk);
            r.nadd(kernel, inner, sk)
        };
        let h4 = {
            let head = kernel.const_(r.nat.succ_mul, vec![]);
            let forward = apply_all(kernel, head, &[k, k]);
            let symm_fv = fv.next();
            let backward = gsymm(
                kernel,
                r.logic,
                nat_ty,
                succ_product,
                square_plus,
                forward,
                symm_fv,
            );
            let cong_fv = fv.next();
            gcongr(
                kernel,
                r.logic,
                nat_ty,
                nat_ty,
                square_plus,
                succ_product,
                backward,
                &|kernel, u| {
                    let inner = r.nadd(kernel, u, sk);
                    r.nadd(kernel, inner, sk)
                },
                cong_fv,
            )
        };

        let t1 = fv.next();
        let t2 = fv.next();
        let t3 = fv.next();
        let chain = gtrans(kernel, r.logic, nat_ty, l0, l1, l2, h1, h2, t1);
        let chain = gtrans(kernel, r.logic, nat_ty, l0, l2, l3, chain, h3, t2);
        let chain = gtrans(kernel, r.logic, nat_ty, l0, l3, l4, chain, h4, t3);

        let ih_ty = claim(kernel, k);
        lams(kernel, &[(k_id, nat_ty), (ih_id, ih_ty)], chain)
    };

    let n_id = fv.next();
    let n = kernel.fvar(n_id);
    let rec = kernel.const_(r.nat.rec, vec![r.zero_lvl]);
    let applied = apply_all(kernel, rec, &[motive, base, step, n]);
    let value = lam_fv(kernel, n_id, nat_ty, applied);
    let ty = {
        let n2_id = fv.next();
        let n2 = kernel.fvar(n2_id);
        let body = claim(kernel, n2);
        pi_fv(kernel, n2_id, nat_ty, body)
    };

    let name = kernel.name_str(r.code_ns, "tri_two");
    kernel.add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value,
    })?;
    Ok(name)
}

/// The `Nat` value of the graph formula's right-hand side:
/// `((a+b)·(a+b) + (a+b)) + (a+a)`.
fn pair_graph_value(kernel: &mut crate::Kernel, r: &Rob, a: ExprId, b: ExprId) -> ExprId {
    let sum = r.nadd(kernel, a, b);
    let square = r.nmul(kernel, sum, sum);
    let left = r.nadd(kernel, square, sum);
    let twice = r.nadd(kernel, a, a);
    r.nadd(kernel, left, twice)
}

/// `FO.Code.pair_two : Π (a b : Nat),
///   Eq Nat (Nat.add (pair a b) (pair a b)) (((a+b)·(a+b) + (a+b)) + (a+a))`.
///
/// `pair a b` δ-unfolds to `tri (a+b) + a`, so the left-hand side is
/// `(tri s + a) + (tri s + a)`; `add_add_add_comm` regroups it to
/// `(tri s + tri s) + (a + a)` and `FO.Code.tri_two` closes it. Two steps.
fn declare_pair_two(
    kernel: &mut crate::Kernel,
    r: &Rob,
    tri_two: NameId,
    fv: &mut Fv,
) -> Result<NameId, KernelError> {
    let nat_ty = r.nat_ty;
    let a_id = fv.next();
    let b_id = fv.next();
    let a = kernel.fvar(a_id);
    let b = kernel.fvar(b_id);

    let sum = r.nadd(kernel, a, b);
    let tri_sum = {
        let head = kernel.const_(r.code_tri, vec![]);
        kernel.app(head, sum)
    };
    let leg = r.nadd(kernel, tri_sum, a);
    let l0 = r.nadd(kernel, leg, leg);
    let doubled = r.nadd(kernel, tri_sum, tri_sum);
    let twice = r.nadd(kernel, a, a);
    let l1 = r.nadd(kernel, doubled, twice);
    let h1 = {
        let head = kernel.const_(r.nat.add_add_add_comm, vec![]);
        apply_all(kernel, head, &[tri_sum, a, tri_sum, a])
    };
    let square = r.nmul(kernel, sum, sum);
    let square_plus = r.nadd(kernel, square, sum);
    let l2 = r.nadd(kernel, square_plus, twice);
    let h2 = {
        let head = kernel.const_(tri_two, vec![]);
        let doubling = kernel.app(head, sum);
        let cong_fv = fv.next();
        gcongr(
            kernel,
            r.logic,
            nat_ty,
            nat_ty,
            doubled,
            square_plus,
            doubling,
            &|kernel, u| r.nadd(kernel, u, twice),
            cong_fv,
        )
    };
    let trans_fv = fv.next();
    let value_body = gtrans(kernel, r.logic, nat_ty, l0, l1, l2, h1, h2, trans_fv);
    let value = lams(kernel, &[(a_id, nat_ty), (b_id, nat_ty)], value_body);

    let ty = {
        let a2_id = fv.next();
        let b2_id = fv.next();
        let a2 = kernel.fvar(a2_id);
        let b2 = kernel.fvar(b2_id);
        let pair_head = kernel.const_(r.code_pair, vec![]);
        let coded = apply_all(kernel, pair_head, &[a2, b2]);
        let lhs = r.nadd(kernel, coded, coded);
        let rhs = pair_graph_value(kernel, r, a2, b2);
        let body = r.neq(kernel, lhs, rhs);
        pis(kernel, &[(a2_id, nat_ty), (b2_id, nat_ty)], body)
    };

    let name = kernel.name_str(r.code_ns, "pair_two");
    kernel.add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value,
    })?;
    Ok(name)
}

/// `FO.Q.pairGraph : FO.Term -> FO.Term -> FO.Term -> FO.Formula
///   := fun x y z => eqf (z + z) (((x + y) · (x + y) + (x + y)) + (x + x))`.
fn declare_pair_graph(
    kernel: &mut crate::Kernel,
    r: &Rob,
    fv: &mut Fv,
) -> Result<NameId, KernelError> {
    let term_ty = r.term_ty;
    let x_id = fv.next();
    let y_id = fv.next();
    let z_id = fv.next();
    let x = kernel.fvar(x_id);
    let y = kernel.fvar(y_id);
    let z = kernel.fvar(z_id);
    let body = pair_graph_formula(kernel, r, x, y, z);
    let value = lams(
        kernel,
        &[(x_id, term_ty), (y_id, term_ty), (z_id, term_ty)],
        body,
    );
    let ty = {
        let inner = arrow(kernel, term_ty, r.formula_ty);
        let middle = arrow(kernel, term_ty, inner);
        arrow(kernel, term_ty, middle)
    };
    let name = kernel.name_str(r.q_ns, "pairGraph");
    kernel.add_declaration(Declaration::Definition {
        name,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(0),
    })?;
    Ok(name)
}

/// `eqf (z + z) (((x + y) · (x + y) + (x + y)) + (x + x))` at given terms.
fn pair_graph_formula(
    kernel: &mut crate::Kernel,
    r: &Rob,
    x: ExprId,
    y: ExprId,
    z: ExprId,
) -> ExprId {
    let lhs = r.tadd(kernel, z, z);
    let rhs = pair_graph_rhs(kernel, r, x, y);
    r.f_eqf(kernel, lhs, rhs)
}

/// `((x + y) · (x + y) + (x + y)) + (x + x)`.
fn pair_graph_rhs(kernel: &mut crate::Kernel, r: &Rob, x: ExprId, y: ExprId) -> ExprId {
    let sum = r.tadd(kernel, x, y);
    let square = r.tmul(kernel, sum, sum);
    let left = r.tadd(kernel, square, sum);
    let twice = r.tadd(kernel, x, x);
    r.tadd(kernel, left, twice)
}

/// `FO.Q.pairFormula : FO.Formula := pairGraph (var 2) (var 1) (var 0)` — the
/// graph as a single formula in three free de Bruijn indices, so the statement
/// "there is a formula defining `FO.Code.pair`" is itself a kernel object.
fn declare_pair_formula(
    kernel: &mut crate::Kernel,
    r: &Rob,
    pair_graph: NameId,
) -> Result<NameId, KernelError> {
    let x = r.tvar(kernel, 2);
    let y = r.tvar(kernel, 1);
    let z = r.tvar(kernel, 0);
    let head = kernel.const_(pair_graph, vec![]);
    let value = apply_all(kernel, head, &[x, y, z]);
    let ty = r.formula_ty;
    let name = kernel.name_str(r.q_ns, "pairFormula");
    kernel.add_declaration(Declaration::Definition {
        name,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(0),
    })?;
    Ok(name)
}

/// `FO.Q.pair_represented : Π (a b : Nat), FO.Provable FO.Q
///   (FO.Q.pairGraph (numeral a) (numeral b) (numeral (FO.Code.pair a b)))`.
///
/// Six Leibniz steps. The first five evaluate the polynomial side down to a
/// single numeral, starting from `FO.Provable.eqf_refl` at the polynomial
/// itself and rewriting one subterm at a time with `FO.Q.add_numeral` /
/// `FO.Q.mul_numeral`; the sixth transfers the result onto
/// `numeral (pair a b) + numeral (pair a b)`, whose own evaluation is
/// `add_numeral` transported along `FO.Code.pair_two`.
fn declare_pair_represented(
    kernel: &mut crate::Kernel,
    r: &Rob,
    subst_numeral: NameId,
    add_numeral: NameId,
    mul_numeral: NameId,
    pair_two: NameId,
    pair_graph: NameId,
    fv: &mut Fv,
) -> Result<NameId, KernelError> {
    let nat_ty = r.nat_ty;
    let a_id = fv.next();
    let b_id = fv.next();
    let a = kernel.fvar(a_id);
    let b = kernel.fvar(b_id);

    let na = r.tnum(kernel, a);
    let nb = r.tnum(kernel, b);
    let big = pair_graph_rhs(kernel, r, na, nb);

    // The `Nat` values the five evaluation steps produce.
    let s1 = r.nadd(kernel, a, b); // a + b
    let s2 = r.nmul(kernel, s1, s1); // (a+b)·(a+b)
    let s3 = r.nadd(kernel, s2, s1); // (a+b)·(a+b) + (a+b)
    let s4 = r.nadd(kernel, a, a); // a + a
    let s5 = r.nadd(kernel, s3, s4); // the whole right-hand side
    let m1 = r.tnum(kernel, s1);
    let m3 = r.tnum(kernel, s3);
    let m5 = r.tnum(kernel, s5);

    // `BIG` as a shape over the two numeral slots `a` and `b`.
    let big_shape = || {
        add(
            add(
                mul(add(num(0), num(1)), add(num(0), num(1))),
                add(num(0), num(1)),
            ),
            add(num(0), num(0)),
        )
    };

    let seed = {
        let head = kernel.const_(r.rules[rule::EQF_REFL], vec![]);
        let q = kernel.const_(r.q_ns, vec![]);
        apply_all(kernel, head, &[q, big])
    };

    // Step 1: (na + nb) -> numeral (a+b), at all three occurrences.
    let after1 = {
        let s = r.tadd(kernel, na, nb);
        let equation = {
            let head = kernel.const_(add_numeral, vec![]);
            apply_all(kernel, head, &[a, b])
        };
        let shape = EqShape {
            lhs: add(add(mul(Tm::Hole, Tm::Hole), Tm::Hole), add(num(0), num(0))),
            rhs: big_shape(),
        };
        let numerals = [a, b];
        let plan = Leibniz {
            numerals: &numerals,
            shape: &shape,
            s,
            t: m1,
        };
        leibniz(kernel, r, subst_numeral, &plan, equation, seed, fv)
    };

    // Step 2: numeral (a+b) · numeral (a+b) -> numeral ((a+b)·(a+b)).
    let after2 = {
        let s = r.tmul(kernel, m1, m1);
        let t = r.tnum(kernel, s2);
        let equation = {
            let head = kernel.const_(mul_numeral, vec![]);
            apply_all(kernel, head, &[s1, s1])
        };
        let shape = EqShape {
            lhs: add(add(Tm::Hole, num(2)), add(num(0), num(0))),
            rhs: big_shape(),
        };
        let numerals = [a, b, s1];
        let plan = Leibniz {
            numerals: &numerals,
            shape: &shape,
            s,
            t,
        };
        leibniz(kernel, r, subst_numeral, &plan, equation, after1, fv)
    };

    // Step 3: numeral ((a+b)·(a+b)) + numeral (a+b) -> numeral of the sum.
    let after3 = {
        let m2 = r.tnum(kernel, s2);
        let s = r.tadd(kernel, m2, m1);
        let equation = {
            let head = kernel.const_(add_numeral, vec![]);
            apply_all(kernel, head, &[s2, s1])
        };
        let shape = EqShape {
            lhs: add(Tm::Hole, add(num(0), num(0))),
            rhs: big_shape(),
        };
        let numerals = [a, b];
        let plan = Leibniz {
            numerals: &numerals,
            shape: &shape,
            s,
            t: m3,
        };
        leibniz(kernel, r, subst_numeral, &plan, equation, after2, fv)
    };

    // Step 4: na + na -> numeral (a + a).
    let after4 = {
        let s = r.tadd(kernel, na, na);
        let t = r.tnum(kernel, s4);
        let equation = {
            let head = kernel.const_(add_numeral, vec![]);
            apply_all(kernel, head, &[a, a])
        };
        let shape = EqShape {
            lhs: add(num(2), Tm::Hole),
            rhs: big_shape(),
        };
        let numerals = [a, b, s3];
        let plan = Leibniz {
            numerals: &numerals,
            shape: &shape,
            s,
            t,
        };
        leibniz(kernel, r, subst_numeral, &plan, equation, after3, fv)
    };

    // Step 5: the last sum collapses, leaving `eqf (numeral s5) BIG`.
    let after5 = {
        let m4 = r.tnum(kernel, s4);
        let s = r.tadd(kernel, m3, m4);
        let equation = {
            let head = kernel.const_(add_numeral, vec![]);
            apply_all(kernel, head, &[s3, s4])
        };
        let shape = EqShape {
            lhs: Tm::Hole,
            rhs: big_shape(),
        };
        let numerals = [a, b];
        let plan = Leibniz {
            numerals: &numerals,
            shape: &shape,
            s,
            t: m5,
        };
        leibniz(kernel, r, subst_numeral, &plan, equation, after4, fv)
    };

    // `numeral (pair a b) + numeral (pair a b) = numeral s5`, by `add_numeral`
    // at the code transported along `FO.Code.pair_two`.
    let coded = {
        let head = kernel.const_(r.code_pair, vec![]);
        apply_all(kernel, head, &[a, b])
    };
    let nc = r.tnum(kernel, coded);
    let doubled_code = r.tadd(kernel, nc, nc);
    let code_eval = {
        let head = kernel.const_(add_numeral, vec![]);
        let raw = apply_all(kernel, head, &[coded, coded]);
        let doubling = {
            let head = kernel.const_(pair_two, vec![]);
            apply_all(kernel, head, &[a, b])
        };
        let raw_sum = r.nadd(kernel, coded, coded);
        let cong_fv = fv.next();
        let formula_eq = gcongr(
            kernel,
            r.logic,
            nat_ty,
            r.formula_ty,
            raw_sum,
            s5,
            doubling,
            &|kernel, value| {
                let numeral = r.tnum(kernel, value);
                let lhs = r.tadd(kernel, nc, nc);
                r.f_eqf(kernel, lhs, numeral)
            },
            cong_fv,
        );
        let from = {
            let numeral = r.tnum(kernel, raw_sum);
            r.f_eqf(kernel, doubled_code, numeral)
        };
        let to = r.f_eqf(kernel, doubled_code, m5);
        cast_derivation(kernel, r, from, to, formula_eq, raw, fv)
    };

    // Step 6: replace `numeral s5` by the polynomial, on the right of the
    // code's own equation. This is the only step whose `p` has the hole on the
    // RIGHT, and it is what turns the evaluation chain back into the graph.
    let derivation = {
        let shape = EqShape {
            lhs: add(num(0), num(0)),
            rhs: Tm::Hole,
        };
        let numerals = [coded];
        let plan = Leibniz {
            numerals: &numerals,
            shape: &shape,
            s: m5,
            t: big,
        };
        leibniz(kernel, r, subst_numeral, &plan, after5, code_eval, fv)
    };

    let value = lams(kernel, &[(a_id, nat_ty), (b_id, nat_ty)], derivation);
    let ty = {
        let a2_id = fv.next();
        let b2_id = fv.next();
        let a2 = kernel.fvar(a2_id);
        let b2 = kernel.fvar(b2_id);
        let na2 = r.tnum(kernel, a2);
        let nb2 = r.tnum(kernel, b2);
        let coded2 = {
            let head = kernel.const_(r.code_pair, vec![]);
            apply_all(kernel, head, &[a2, b2])
        };
        let nc2 = r.tnum(kernel, coded2);
        let head = kernel.const_(pair_graph, vec![]);
        let formula = apply_all(kernel, head, &[na2, nb2, nc2]);
        let body = r.prov_q(kernel, formula);
        pis(kernel, &[(a2_id, nat_ty), (b2_id, nat_ty)], body)
    };

    let name = kernel.name_str(r.q_ns, "pair_represented");
    kernel.add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value,
    })?;
    Ok(name)
}

#[cfg(test)]
mod tests;
