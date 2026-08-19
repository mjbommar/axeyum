//! A **machine-checked model of the `Real` axiom package in the constructed
//! `CReal`** — ADR-0512 phase R4, and the step that supersedes
//! [`build_int_model_of_arith`](crate::build_int_model_of_arith).
//!
//! ## What changed, and why it needed a new module
//!
//! [`build_int_model_of_arith`] interprets the `Real` package in `ℤ` by
//! renaming eight constants, and it is careful about what that buys: relative
//! consistency, not a discharge. Its own module docs say it outright — **`Int`
//! is not ℝ**, so a theorem obtained by instantiating the interface there is a
//! theorem about the integers.
//!
//! The `ℚ` model in `rat_prelude::model` then carried out the first half of `arith_model`'s
//! own prescription — "constructing a carrier (`ℚ` suffices for every axiom in
//! the package)" — and it is a *field*, which is where a Farkas refutation's
//! multipliers live. It is still not ℝ. The package has no completeness,
//! Archimedean or density axiom, so ℚ satisfying it says nothing about the
//! reals; `√2` is the standing counterexample to reading it that way.
//!
//! [`build_creal_model_of_arith`] is the third model in that ladder and the
//! only one at a carrier that *is* the real numbers:
//! [`CReal`](crate::CRealPrelude), a Bishop setoid of regular ℚ-sequences over
//! the constructed ℚ, built in [`creal`](crate::build_creal_prelude) at **zero**
//! trusted declarations. One thing about the interpretation has to change to
//! make that possible, and it is the whole content of ADR-0512:
//!
//! > **Nine of the 22 laws are stated with the kernel's `Eq`, and `Eq CReal` is
//! > not the equality of real numbers.** `CReal.Equiv` is.
//!
//! So the interpretation is not a constant renaming. It is a constant renaming
//! **plus** the rewrite that replaces the partial application `Eq Real` — the
//! `Eq` of the carrier, and only that one — with `CReal.Equiv`. That is the
//! same rewrite ADR-0512 phase R3 applies to the consumer telescope's nine
//! `Eq`-laws (`ordered_ring::setoid::rewrite_eq_at_real` in `axeyum-solver`);
//! here it is applied to the axioms themselves, so what the kernel checks is
//! that `CReal` **satisfies the interface phase R3 abstracts over**.
//!
//! ## The discipline, unchanged from `arith_model`
//!
//! For each of the 22 `Real` laws this module admits
//!
//! ```text
//! Real.CRealModel.<law> : ⟦ type of Real.<law> ⟧    := CReal.<law>
//! ```
//!
//! where `⟦·⟧` is computed **from the axiom as it stands in the environment**,
//! never written out here. Two consequences, both deliberate:
//!
//! - an axiom whose statement changes changes the obligation, rather than the
//!   two developments drifting apart while both stay green; and
//! - an axiom `CReal` does **not** satisfy makes this function return `Err`.
//!   There is no row to drop silently: the kernel type-checks `CReal.<law>`
//!   against the interpreted type at admission.
//!
//! That second point is what makes the `Eq`-rewrite self-guarding. If the
//! rewrite failed to fire on one of the nine, the interpreted type would read
//! `Eq CReal …` and the supplied proof — whose type is `CReal.Equiv …` — would
//! be **rejected**. Nothing here has to trust that the rewrite worked.
//!
//! ## What this establishes, stated exactly
//!
//! - Every one of the 22 laws holds of a carrier constructed from nothing, so
//!   each witness carries an empty
//!   [`axiom_footprint`](crate::Kernel::axiom_footprint). ADR-0456's caveat
//!   that the model was `ℤ` and `ℤ` is not ℝ is **discharged**: the carrier is
//!   ℝ, and `CReal.ofRat` embeds ℚ into it.
//! - Thirteen laws are modelled **verbatim** and nine only after `Eq Real` is
//!   read as `CReal.Equiv`. [`CRealModelLaw::restated_over_equiv`] records
//!   which, per law, so ADR-0512's Measurement 2 (9 vs 21) is read out of the
//!   kernel rather than quoted.
//! - What it does **not** establish is that `Eq CReal` is real-number equality.
//!   It is not, and no witness here says it is. A consumer that wants its
//!   equality reasoning back must go through the phase R3 telescope's equality
//!   slot, which is exactly the shape this model satisfies. This is the one
//!   respect in which the ℤ and ℚ models are *stronger*: both interpret ring
//!   equality by the kernel's own `Eq`, and neither is ℝ. The three models are
//!   complements, and it is precisely the nine laws that separate them.
//! - As in `arith_model`, the step from "every axiom translates" to "every
//!   *derivation* translates" is the standard homomorphism argument over the
//!   term language and is not itself machine-checked — the kernel cannot state
//!   it.
//!
//! ## Vacuity, and why footprints cannot see it
//!
//! An empty footprint says a witness rests on nothing. It does not say the
//! witness says anything. Six of `CReal`'s seven strict-order laws hold,
//! footprint-free, of the **empty** relation; `mul_zero`, `mul_one` and
//! `sq_nonneg` all hold of a `mul` returning zero everywhere. The seven
//! discrimination witnesses that close those holes live in
//! [`CRealPrelude`](crate::CRealPrelude) and are checked by
//! `examples/creal_model_witness.rs` — **presence first, then footprint**,
//! because `axiom_footprint` of an interned-but-undeclared name is the empty
//! vector and a footprint test alone passes with the witness deleted.

use std::collections::HashMap;

use crate::arith_model::{declaration_type, interpret, leaf_name};
use crate::arith_prelude::{ArithPrelude, build_arith_prelude};
use crate::creal::{CRealPrelude, build_creal_prelude};
use crate::env::Declaration;
use crate::expr::{ExprId, ExprNode};
use crate::name::NameId;
use crate::{Kernel, KernelError};

/// One interpreted law: the `Real` axiom, the `CReal` theorem that models it,
/// and the kernel-checked witness declaration binding them.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CRealModelLaw {
    /// The `Real` axiom being interpreted.
    pub real: NameId,
    /// The `CReal` theorem supplied as its proof under the interpretation.
    pub creal: NameId,
    /// The admitted witness `Real.CRealModel.<law>`, whose type is the
    /// *computed* interpretation of `real`'s type.
    pub witness: NameId,
    /// Whether the interpreted `Real` type is **syntactically identical** to
    /// the `CReal` theorem's own declared type, up to binder names and binder
    /// info (both of which are irrelevant to what a `∀` says, and neither of
    /// which the two developments were written to agree on).
    ///
    /// Recorded because identity is the stronger and more auditable outcome
    /// than definitional equality: it means the `Real` axiom and the `CReal`
    /// theorem say the same thing symbol for symbol, rather than merely
    /// something the conversion checker can reconcile.
    pub identical: bool,
    /// Whether the `Eq Real ↦ CReal.Equiv` rewrite **fired** on this law — i.e.
    /// whether this is one of the nine that ADR-0512 says the setoid route can
    /// only satisfy in restated form.
    ///
    /// Read out of the axiom, not asserted: `restated_over_equiv` is true for
    /// exactly the laws whose type mentions the carrier's `Eq`.
    pub restated_over_equiv: bool,
}

/// The result of [`build_creal_model_of_arith`]: both developments, the symbol
/// interpretation, and one checked witness per law.
#[derive(Debug, Clone)]
pub struct CRealModel {
    /// The axiomatized `Real` package being modelled.
    pub arith: ArithPrelude,
    /// The constructed `CReal` development doing the modelling.
    pub creal: CRealPrelude,
    /// The interpretation of `Real`'s eight carrier/operation symbols, as
    /// `(Real symbol, CReal symbol)` pairs in declaration order.
    pub symbols: Vec<(NameId, NameId)>,
    /// The equality slot: `(Eq, CReal.Equiv)`. Not a constant renaming — `Eq`
    /// is polymorphic and `CReal.Equiv` is not, so the partial application
    /// `Eq Real` is what gets replaced.
    pub equality: (NameId, NameId),
    /// One entry per `Real` law, in declaration order.
    pub laws: Vec<CRealModelLaw>,
}

impl CRealModel {
    /// The witness declarations, for footprint checks.
    #[must_use]
    pub fn witnesses(&self) -> Vec<NameId> {
        self.laws.iter().map(|law| law.witness).collect()
    }

    /// How many of the 22 laws needed restating over `CReal.Equiv`. ADR-0512
    /// Measurement 2 says nine; this counts them in the kernel.
    #[must_use]
    pub fn restated_count(&self) -> usize {
        self.laws
            .iter()
            .filter(|law| law.restated_over_equiv)
            .count()
    }
}

/// Build the `Real` package and the constructed `CReal` development, and admit
/// the interpretation of every `Real` law into `CReal`.
///
/// The witness types are computed by rewriting `Eq Real` to `CReal.Equiv` and
/// substituting the interpreted symbols into the `Real` axioms **as they stand
/// in the environment**, so an axiom whose statement changes changes the
/// obligation, and an axiom that `CReal` does not satisfy makes this function
/// fail rather than silently drop a row.
///
/// # Errors
///
/// Returns the trusted gate's rejection. A [`KernelError`] from
/// `add_declaration` here means the kernel **refused** a `CReal` theorem as a
/// proof of the interpreted `Real` axiom — i.e. the constructed reals were not
/// shown to model that axiom. In particular a `TypeMismatch` on one of the nine
/// `Eq`-laws is what a broken equality rewrite looks like: the obligation would
/// still read `Eq CReal …` while the proof proves `CReal.Equiv …`.
pub fn build_creal_model_of_arith(kernel: &mut Kernel) -> Result<CRealModel, KernelError> {
    let arith = build_arith_prelude(kernel)?;
    let creal = build_creal_prelude(kernel)?;

    let symbols = vec![
        (arith.r, creal.creal),
        (arith.add, creal.add),
        (arith.mul, creal.mul),
        (arith.neg, creal.neg),
        (arith.zero, creal.zero),
        (arith.one, creal.one),
        (arith.le, creal.le),
        (arith.lt, creal.lt),
    ];
    let interpretation: HashMap<NameId, NameId> = symbols.iter().copied().collect();
    let equiv = kernel.const_(creal.equiv, vec![]);

    let anon = kernel.anon();
    let model_root = {
        let real = kernel.name_str(anon, "Real");
        kernel.name_str(real, "CRealModel")
    };

    let mut laws = Vec::with_capacity(22);
    for (real, creal_law) in arith
        .ordered_ring_laws()
        .into_iter()
        .zip(creal.ordered_ring_laws())
    {
        let real_ty = declaration_type(kernel, real)?;
        let creal_ty = declaration_type(kernel, creal_law)?;

        // The equality slot first: `Eq Real` is matched on the *un-interpreted*
        // axiom, where the carrier is still the `Real` constant.
        let (restated_ty, restated_over_equiv) =
            rewrite_eq_at_carrier(kernel, real_ty, arith.logic.eq, arith.r, equiv);
        // ...and then the eight-symbol renaming over what is left.
        let mut memo = HashMap::new();
        let interpreted = interpret(kernel, restated_ty, &interpretation, &mut memo);

        let witness = {
            let leaf = leaf_name(kernel, real);
            kernel.name_str(model_root, leaf)
        };
        let value = kernel.const_(creal_law, vec![]);
        kernel.add_declaration(Declaration::Theorem {
            name: witness,
            uparams: vec![],
            ty: interpreted,
            value,
        })?;

        let identical = {
            let a = erase_binder_names(kernel, interpreted, anon, &mut HashMap::new());
            let b = erase_binder_names(kernel, creal_ty, anon, &mut HashMap::new());
            a == b
        };
        laws.push(CRealModelLaw {
            real,
            creal: creal_law,
            witness,
            identical,
            restated_over_equiv,
        });
    }

    Ok(CRealModel {
        arith,
        creal,
        symbols,
        equality: (arith.logic.eq, creal.equiv),
        laws,
    })
}

/// Replace the partial application `<eq_name> <carrier>` — the carrier's own
/// equality, and nothing else — by `replacement`, reporting whether it fired.
///
/// This is the operation a constant renaming cannot express: `Eq` is
/// polymorphic (`∀ {α : Sort u}, α → α → Prop`) while a setoid's equality is a
/// relation on one carrier, so the two constants do not have the same arity and
/// no map from `Eq` alone is type-correct. Matching the *application* of `Eq` to
/// the carrier is what lines the arities up: the two remaining arguments are
/// carried through untouched and interpreted with everything else.
///
/// The narrowness matters. An `Eq` at any other type — `Eq Nat`, `Eq Rat`
/// inside an unfolded definition — is left alone, because the model replaces
/// real-number equality and makes no claim about the rest of the term language.
fn rewrite_eq_at_carrier(
    kernel: &mut Kernel,
    e: ExprId,
    eq_name: NameId,
    carrier: NameId,
    replacement: ExprId,
) -> (ExprId, bool) {
    let mut memo = HashMap::new();
    let mut fired = false;
    let out = rewrite_aux(
        kernel,
        e,
        eq_name,
        carrier,
        replacement,
        &mut fired,
        &mut memo,
    );
    (out, fired)
}

fn rewrite_aux(
    kernel: &mut Kernel,
    e: ExprId,
    eq_name: NameId,
    carrier: NameId,
    replacement: ExprId,
    fired: &mut bool,
    memo: &mut HashMap<ExprId, ExprId>,
) -> ExprId {
    if let Some(&hit) = memo.get(&e) {
        return hit;
    }
    let rebuilt = match kernel.expr_node(e).clone() {
        ExprNode::BVar(_)
        | ExprNode::FVar(_)
        | ExprNode::Sort(_)
        | ExprNode::Lit(_)
        | ExprNode::Const(..) => e,
        ExprNode::App(fun, arg) => {
            if matches!(kernel.expr_node(fun), ExprNode::Const(n, _) if *n == eq_name)
                && matches!(kernel.expr_node(arg), ExprNode::Const(n, _) if *n == carrier)
            {
                *fired = true;
                replacement
            } else {
                let fun = rewrite_aux(kernel, fun, eq_name, carrier, replacement, fired, memo);
                let arg = rewrite_aux(kernel, arg, eq_name, carrier, replacement, fired, memo);
                kernel.app(fun, arg)
            }
        }
        ExprNode::Proj(ty, field, structure) => {
            let structure = rewrite_aux(
                kernel,
                structure,
                eq_name,
                carrier,
                replacement,
                fired,
                memo,
            );
            kernel.proj(ty, field, structure)
        }
        ExprNode::Lam(name, ty, body, info) => {
            let ty = rewrite_aux(kernel, ty, eq_name, carrier, replacement, fired, memo);
            let body = rewrite_aux(kernel, body, eq_name, carrier, replacement, fired, memo);
            kernel.lam(name, ty, body, info)
        }
        ExprNode::Pi(name, ty, body, info) => {
            let ty = rewrite_aux(kernel, ty, eq_name, carrier, replacement, fired, memo);
            let body = rewrite_aux(kernel, body, eq_name, carrier, replacement, fired, memo);
            kernel.pi(name, ty, body, info)
        }
        ExprNode::Let(name, ty, value, body) => {
            let ty = rewrite_aux(kernel, ty, eq_name, carrier, replacement, fired, memo);
            let value = rewrite_aux(kernel, value, eq_name, carrier, replacement, fired, memo);
            let body = rewrite_aux(kernel, body, eq_name, carrier, replacement, fired, memo);
            kernel.let_(name, ty, value, body)
        }
    };
    memo.insert(e, rebuilt);
    rebuilt
}

/// Rebuild `e` with every binder renamed to the anonymous name.
///
/// Used only to decide [`CRealModelLaw::identical`]. Binder names are display
/// data — they do not participate in definitional equality and the two
/// developments were written with different conventions (`a b c` under `Real`,
/// `x y z` under `CReal`) — so comparing interned ids without erasing them
/// would report "drifted" for every law and measure nothing.
fn erase_binder_names(
    kernel: &mut Kernel,
    e: ExprId,
    anon: NameId,
    memo: &mut HashMap<ExprId, ExprId>,
) -> ExprId {
    if let Some(&hit) = memo.get(&e) {
        return hit;
    }
    let rebuilt = match kernel.expr_node(e).clone() {
        ExprNode::BVar(_)
        | ExprNode::FVar(_)
        | ExprNode::Sort(_)
        | ExprNode::Lit(_)
        | ExprNode::Const(..) => e,
        ExprNode::App(fun, arg) => {
            let fun = erase_binder_names(kernel, fun, anon, memo);
            let arg = erase_binder_names(kernel, arg, anon, memo);
            kernel.app(fun, arg)
        }
        ExprNode::Proj(ty, field, structure) => {
            let structure = erase_binder_names(kernel, structure, anon, memo);
            kernel.proj(ty, field, structure)
        }
        ExprNode::Lam(_, ty, body, info) => {
            let ty = erase_binder_names(kernel, ty, anon, memo);
            let body = erase_binder_names(kernel, body, anon, memo);
            kernel.lam(anon, ty, body, info)
        }
        ExprNode::Pi(_, ty, body, info) => {
            let ty = erase_binder_names(kernel, ty, anon, memo);
            let body = erase_binder_names(kernel, body, anon, memo);
            kernel.pi(anon, ty, body, info)
        }
        ExprNode::Let(_, ty, value, body) => {
            let ty = erase_binder_names(kernel, ty, anon, memo);
            let value = erase_binder_names(kernel, value, anon, memo);
            let body = erase_binder_names(kernel, body, anon, memo);
            kernel.let_(anon, ty, value, body)
        }
    };
    memo.insert(e, rebuilt);
    rebuilt
}

#[cfg(test)]
mod creal_model_tests;
