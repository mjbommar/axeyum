//! `ℚ` as a **machine-checked model** of the `AxReal` axiom package.
//!
//! [`build_int_model_of_arith`](crate::build_int_model_of_arith) already
//! exhibits `ℤ` as a model of all 22 `AxReal` laws, and its own doc comment is
//! careful about what that does and does not buy:
//!
//! > Discharging them requires either constructing a carrier (`ℚ` suffices for
//! > every axiom in the package; `ℝ` is needed only once a completeness axiom
//! > is added) or parameterising the consumers over the ordered-ring interface.
//!
//! This is the first half of that sentence, carried out. The `AxReal` package
//! declares no inverse, no division, no completeness, no Archimedean and no
//! density axiom (ADR-0456), so **`ℚ` satisfies every axiom in it** — and
//! unlike `ℤ`, `ℚ` is a *field*, which is what a Farkas refutation's rational
//! multipliers actually live in.
//!
//! What is checked here is the same as for `ℤ`, and no more: the interpretation
//! of each **axiom**, one declaration at a time, with the obligation *computed*
//! from the axiom as it stands in the environment rather than written by hand.
//! The step from "every axiom translates" to "every derivation translates" is
//! the standard homomorphism argument over the term language and is not itself
//! machine-checked — the kernel has no way to state it.

use std::collections::HashMap;

use super::{RatPrelude, build_rat_prelude};
use crate::arith_model::{declaration_type, interpret, leaf_name};
use crate::arith_prelude::{ArithPrelude, build_arith_prelude};
use crate::env::Declaration;
use crate::name::NameId;
use crate::{Kernel, KernelError};

/// One interpreted law: the `AxReal` axiom, the `Rat` theorem that models it, and
/// the kernel-checked witness binding them.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct RatModelLaw {
    /// The `AxReal` axiom being interpreted.
    pub real: NameId,
    /// The `Rat` theorem supplied as its proof under the interpretation.
    pub rat: NameId,
    /// The admitted witness `AxReal.RatModel.<law>`, whose type is the *computed*
    /// interpretation of `real`'s type.
    pub witness: NameId,
    /// Whether the interpreted `AxReal` type is **syntactically identical** to the
    /// `Rat` theorem's own declared type, rather than merely definitionally
    /// equal. Identity is the stronger and more auditable outcome.
    pub identical: bool,
}

/// The result of [`build_rat_model_of_arith`].
#[derive(Debug, Clone)]
pub struct RatModel {
    /// The axiomatized `AxReal` package being modelled.
    pub arith: ArithPrelude,
    /// The constructed `ℚ` development doing the modelling.
    pub rat: RatPrelude,
    /// The interpretation of `AxReal`'s eight carrier/operation symbols.
    pub symbols: Vec<(NameId, NameId)>,
    /// One entry per `AxReal` law, in declaration order.
    pub laws: Vec<RatModelLaw>,
}

impl RatModel {
    /// The witness declarations, for footprint checks.
    #[must_use]
    pub fn witnesses(&self) -> Vec<NameId> {
        self.laws.iter().map(|law| law.witness).collect()
    }
}

/// Build both preludes and admit the interpretation of every `AxReal` law into
/// the constructed `ℚ` development.
///
/// # Errors
///
/// Returns the trusted gate's rejection. A [`KernelError`] from
/// `add_declaration` here means the kernel **refused** a `Rat` theorem as a
/// proof of the interpreted `AxReal` axiom — i.e. `ℚ` was not shown to model that
/// axiom.
pub fn build_rat_model_of_arith(kernel: &mut Kernel) -> Result<RatModel, KernelError> {
    let arith = build_arith_prelude(kernel)?;
    let rat = build_rat_prelude(kernel)?;

    let symbols = vec![
        (arith.r, rat.int.rat),
        (arith.add, rat.int.rat_add),
        (arith.mul, rat.int.rat_mul),
        (arith.neg, rat.int.rat_neg),
        (arith.zero, rat.zero),
        (arith.one, rat.one),
        (arith.le, rat.le),
        (arith.lt, rat.lt),
    ];
    let interpretation: HashMap<NameId, NameId> = symbols.iter().copied().collect();

    // The `AxReal` laws in declaration order, paired with `RatPrelude::ring_laws`
    // — which is written in that same order, so the two lists cannot drift.
    let real_laws: [NameId; 22] = [
        arith.le_refl,
        arith.le_trans,
        arith.lt_irrefl,
        arith.lt_trans,
        arith.lt_of_lt_of_le,
        arith.lt_of_le_of_lt,
        arith.le_of_lt,
        arith.add_le_add,
        arith.add_comm,
        arith.add_assoc,
        arith.add_zero,
        arith.add_neg,
        arith.mul_le_mul_of_nonneg_left,
        arith.zero_lt_one,
        arith.add_lt_add_of_le_of_lt,
        arith.mul_comm,
        arith.mul_assoc,
        arith.mul_one,
        arith.mul_zero,
        arith.left_distrib,
        arith.mul_nonneg,
        arith.sq_nonneg,
    ];
    let rat_laws = rat.ring_laws();

    let anon = kernel.anon();
    let model_root = {
        let real = kernel.name_str(anon, "AxReal");
        kernel.name_str(real, "RatModel")
    };

    let mut laws = Vec::with_capacity(real_laws.len());
    for (real, rat_law) in real_laws.into_iter().zip(rat_laws) {
        let real_ty = declaration_type(kernel, real)?;
        let rat_ty = declaration_type(kernel, rat_law)?;
        let mut memo = HashMap::new();
        let interpreted = interpret(kernel, real_ty, &interpretation, &mut memo);
        let witness = {
            let leaf = leaf_name(kernel, real);
            kernel.name_str(model_root, leaf)
        };
        let value = kernel.const_(rat_law, vec![]);
        kernel.add_declaration(Declaration::Theorem {
            name: witness,
            uparams: vec![],
            ty: interpreted,
            value,
        })?;
        laws.push(RatModelLaw {
            real,
            rat: rat_law,
            witness,
            identical: interpreted == rat_ty,
        });
    }

    Ok(RatModel {
        arith,
        rat,
        symbols,
        laws,
    })
}
