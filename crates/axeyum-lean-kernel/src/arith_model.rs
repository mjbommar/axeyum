//! A **machine-checked model** of the `Real` axiom package, interpreted in the
//! constructed, axiom-free `Int` development.
//!
//! ## Why this exists
//!
//! [`build_arith_prelude`] declares 30 trusted constants under `Real` and its
//! doc comment calls them "an axiomatized **linear ordered field**". Enumerate
//! them and that description is wrong in a way that changes what has to be
//! built: the package declares **no multiplicative inverse, no division, no
//! completeness (supremum) axiom, no Archimedean axiom and no density axiom**.
//! Eight declarations are the carrier and its operations
//! (`Real`, `add`, `mul`, `neg`, `zero`, `one`, `le`, `lt`) and the remaining
//! 22 are the laws of a **commutative ring with `1`, compatibly ordered** —
//! every one of which is true of `ℤ`.
//!
//! That matters because `ℤ` is *constructed* here (see
//! [`build_int_prelude`](crate::build_int_prelude)) and its laws are theorems
//! with an empty [`axiom_footprint`](crate::Kernel::axiom_footprint), whereas
//! `ℝ` cannot be constructed in this kernel at all today — the quotient package
//! is `Quot`/`Quot.mk`/`Quot.lift`/`Quot.ind` and contains **no `Quot.sound`**,
//! so a Cauchy-sequence quotient is not merely expensive, it is inexpressible.
//! ADR-0456 carries the full accounting.
//!
//! ## What this module establishes, and what it does not
//!
//! [`build_int_model_of_arith`] declares, for each of the 22 `Real` **laws**, a
//! theorem
//!
//! ```text
//! Real.IntModel.<law> : ⟦ type of Real.<law> ⟧    := Int.<law>
//! ```
//!
//! where `⟦·⟧` is the constant substitution `Real ↦ Int`, `Real.add ↦ Int.add`,
//! …, `Real.lt ↦ Int.lt` applied to the axiom's type. The interpreted type is
//! **computed from the axiom actually in the environment**, never written by
//! hand, and the kernel then type-checks the `Int` theorem against it at
//! admission. Every witness carries an empty axiom footprint.
//!
//! The consequence is a **relative consistency** statement: the `Real` axiom
//! set has a model whose theory is derived from nothing, so no `Real`-based
//! reconstruction is vacuous on account of a contradictory axiom package. Be
//! precise about the strength of that claim:
//!
//! - What the kernel checks is the interpretation of each **axiom**, one
//!   declaration at a time. That is the base case of the syntactic translation.
//! - The step from "every axiom translates" to "every *derivation* translates"
//!   is the standard homomorphism argument over the term language, and it is
//!   **not** itself machine-checked here — the kernel has no way to state it.
//! - Interpreting `Real` as `ℤ` does **not** discharge the `Real` axioms. A
//!   theorem about `Int` is weaker than the same theorem about `ℝ`, and this
//!   module never claims otherwise. Discharging them requires either
//!   constructing a carrier (`ℚ` suffices for every axiom in the package; `ℝ`
//!   is needed only once a completeness axiom is added) or parameterising the
//!   consumers over the ordered-ring interface so the laws become hypotheses.
//!
//! The completeness of the interpretation is itself tested: every `Real.*`
//! declaration in the environment must be either an interpreted symbol or a
//! law with a witness, so a future 31st axiom cannot slip past this module
//! while the count still reads "all covered".

use std::collections::HashMap;

use crate::arith_prelude::{ArithPrelude, build_arith_prelude};
use crate::env::Declaration;
use crate::expr::{ExprId, ExprNode};
use crate::int_prelude::{IntPrelude, build_int_prelude};
use crate::name::NameId;
use crate::{Kernel, KernelError};

/// One interpreted law: the `Real` axiom, the `Int` theorem that models it, and
/// the kernel-checked witness declaration binding them.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ArithModelLaw {
    /// The `Real` axiom being interpreted.
    pub real: NameId,
    /// The `Int` theorem supplied as its proof under the interpretation.
    pub int: NameId,
    /// The admitted witness `Real.IntModel.<law>`, whose type is the
    /// *computed* interpretation of `real`'s type.
    pub witness: NameId,
    /// Whether the interpreted `Real` type is **syntactically identical** to
    /// the `Int` theorem's own declared type (rather than merely definitionally
    /// equal). Recorded because identity is the stronger and more auditable
    /// outcome, and because a law where it fails is a law whose two statements
    /// were written differently and deserves a second look.
    pub identical: bool,
}

/// The result of [`build_int_model_of_arith`]: both preludes, the symbol
/// interpretation, and one checked witness per law.
#[derive(Debug, Clone)]
pub struct ArithModel {
    /// The axiomatized `Real` package being modelled.
    pub arith: ArithPrelude,
    /// The constructed `Int` development doing the modelling.
    pub int: IntPrelude,
    /// The interpretation of `Real`'s eight carrier/operation symbols, as
    /// `(Real symbol, Int symbol)` pairs in declaration order.
    pub symbols: Vec<(NameId, NameId)>,
    /// One entry per `Real` law, in declaration order.
    pub laws: Vec<ArithModelLaw>,
}

impl ArithModel {
    /// The witness declarations, for footprint checks.
    #[must_use]
    pub fn witnesses(&self) -> Vec<NameId> {
        self.laws.iter().map(|law| law.witness).collect()
    }
}

/// Build both preludes and admit the interpretation of every `Real` law into
/// the constructed `Int` development.
///
/// The witness types are computed by substituting the interpreted symbols into
/// the `Real` axioms **as they stand in the environment**, so an axiom whose
/// statement changes changes the obligation, and an axiom that `ℤ` does not
/// satisfy makes this function fail rather than silently drop a row.
///
/// # Errors
///
/// Returns the trusted gate's rejection. In particular a
/// [`KernelError`] from `add_declaration` here means the kernel **refused** an
/// `Int` theorem as a proof of the interpreted `Real` axiom — i.e. `ℤ` was not
/// shown to model that axiom.
pub fn build_int_model_of_arith(kernel: &mut Kernel) -> Result<ArithModel, KernelError> {
    let arith = build_arith_prelude(kernel)?;
    let int = build_int_prelude(kernel)?;

    let symbols = vec![
        (arith.r, int.z),
        (arith.add, int.add),
        (arith.mul, int.mul),
        (arith.neg, int.neg),
        (arith.zero, int.zero),
        (arith.one, int.one),
        (arith.le, int.le),
        (arith.lt, int.lt),
    ];
    let interpretation: HashMap<NameId, NameId> = symbols.iter().copied().collect();

    let pairs: [(NameId, NameId); 22] = [
        (arith.le_refl, int.le_refl),
        (arith.le_trans, int.le_trans),
        (arith.lt_irrefl, int.lt_irrefl),
        (arith.lt_trans, int.lt_trans),
        (arith.lt_of_lt_of_le, int.lt_of_lt_of_le),
        (arith.lt_of_le_of_lt, int.lt_of_le_of_lt),
        (arith.le_of_lt, int.le_of_lt),
        (arith.add_le_add, int.add_le_add),
        (arith.add_comm, int.add_comm),
        (arith.add_assoc, int.add_assoc),
        (arith.add_zero, int.add_zero),
        (arith.add_neg, int.add_neg),
        (
            arith.mul_le_mul_of_nonneg_left,
            int.mul_le_mul_of_nonneg_left,
        ),
        (arith.zero_lt_one, int.zero_lt_one),
        (arith.add_lt_add_of_le_of_lt, int.add_lt_add_of_le_of_lt),
        (arith.mul_comm, int.mul_comm),
        (arith.mul_assoc, int.mul_assoc),
        (arith.mul_one, int.mul_one),
        (arith.mul_zero, int.mul_zero),
        (arith.left_distrib, int.left_distrib),
        (arith.mul_nonneg, int.mul_nonneg),
        (arith.sq_nonneg, int.sq_nonneg),
    ];

    let anon = kernel.anon();
    let model_root = {
        let real = kernel.name_str(anon, "Real");
        kernel.name_str(real, "IntModel")
    };

    let mut laws = Vec::with_capacity(pairs.len());
    for (real, int_law) in pairs {
        let real_ty = declaration_type(kernel, real)?;
        let int_ty = declaration_type(kernel, int_law)?;
        let mut memo = HashMap::new();
        let interpreted = interpret(kernel, real_ty, &interpretation, &mut memo);
        let witness = {
            let leaf = leaf_name(kernel, real);
            kernel.name_str(model_root, leaf)
        };
        let value = kernel.const_(int_law, vec![]);
        kernel.add_declaration(Declaration::Theorem {
            name: witness,
            uparams: vec![],
            ty: interpreted,
            value,
        })?;
        laws.push(ArithModelLaw {
            real,
            int: int_law,
            witness,
            identical: interpreted == int_ty,
        });
    }

    Ok(ArithModel {
        arith,
        int,
        symbols,
        laws,
    })
}

/// The declared type of `name`, or [`KernelError::UnknownConst`] if the
/// environment does not carry it.
fn declaration_type(kernel: &Kernel, name: NameId) -> Result<ExprId, KernelError> {
    kernel
        .environment()
        .get(name)
        .map(Declaration::ty)
        .ok_or(KernelError::UnknownConst { name })
}

/// The final component of a dotted name (`Real.add_comm` ↦ `add_comm`).
fn leaf_name(kernel: &Kernel, name: NameId) -> String {
    let rendered = kernel.display_name(name).to_string();
    rendered
        .rsplit('.')
        .next()
        .unwrap_or(rendered.as_str())
        .to_string()
}

/// Rebuild `e` with every constant in `map` replaced by its image, sharing
/// unchanged subterms.
///
/// Universe arguments, binder names and binder info are carried through
/// untouched: the interpretation renames constants and nothing else, which is
/// what makes the resulting obligation the `Real` axiom rather than a
/// convenient restatement of it.
fn interpret(
    kernel: &mut Kernel,
    e: ExprId,
    map: &HashMap<NameId, NameId>,
    memo: &mut HashMap<ExprId, ExprId>,
) -> ExprId {
    if let Some(&hit) = memo.get(&e) {
        return hit;
    }
    let node = kernel.expr_node(e).clone();
    let rebuilt = match node {
        ExprNode::BVar(_) | ExprNode::FVar(_) | ExprNode::Sort(_) | ExprNode::Lit(_) => e,
        ExprNode::Const(name, levels) => match map.get(&name) {
            Some(&image) => kernel.const_(image, levels),
            None => e,
        },
        ExprNode::Proj(ty, field, structure) => {
            let structure = interpret(kernel, structure, map, memo);
            kernel.proj(ty, field, structure)
        }
        ExprNode::App(fun, arg) => {
            let fun = interpret(kernel, fun, map, memo);
            let arg = interpret(kernel, arg, map, memo);
            kernel.app(fun, arg)
        }
        ExprNode::Lam(name, ty, body, info) => {
            let ty = interpret(kernel, ty, map, memo);
            let body = interpret(kernel, body, map, memo);
            kernel.lam(name, ty, body, info)
        }
        ExprNode::Pi(name, ty, body, info) => {
            let ty = interpret(kernel, ty, map, memo);
            let body = interpret(kernel, body, map, memo);
            kernel.pi(name, ty, body, info)
        }
        ExprNode::Let(name, ty, value, body) => {
            let ty = interpret(kernel, ty, map, memo);
            let value = interpret(kernel, value, map, memo);
            let body = interpret(kernel, body, map, memo);
            kernel.let_(name, ty, value, body)
        }
    };
    memo.insert(e, rebuilt);
    rebuilt
}

#[cfg(test)]
mod arith_model_tests;
