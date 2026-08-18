//! Parameterising a finished LRA/Farkas refutation over the **ordered-ring
//! interface**, so the refutation stops being a statement *about* the `Real`
//! prelude's 30 trusted constants and becomes a statement about every structure
//! that satisfies its 22 laws.
//!
//! ## The move
//!
//! [`reconstruct_lra_proof`](super::reconstruct_lra_proof) returns a term of
//! type `False` whose [`Kernel::axiom_footprint`] is the `Real` prelude's 30
//! declarations, plus one opaque `R`-typed axiom per real variable and one
//! hypothesis axiom per asserted constraint. ADR-0456 measured what those 30
//! are: eight carrier/operation symbols and 22 laws of an **ordered commutative
//! ring with `1`** — no inverse, no division, no completeness, no Archimedean
//! axiom, not even totality. Nothing in the package distinguishes `ℝ` from `ℚ`
//! or from `ℤ`, and `build_int_model_of_arith` exhibits `ℤ` as a model of all
//! 22 with empty footprints.
//!
//! A Farkas refutation only ever invokes those laws. So every one of them can
//! be **λ-abstracted out of the proof term**: replace each `Const` by a bound
//! variable and wrap the term in the corresponding binder telescope. What comes
//! back is
//!
//! ```text
//! ∀ (R : Type) (add mul : R → R → R) (neg : R → R) (zero one : R)
//!   (le lt : R → R → Prop),
//!   <the 22 laws, as hypotheses> →
//!   ∀ (x₀ … x_{n-1} : R), <the asserted constraints, as hypotheses> → False
//! ```
//!
//! and its axiom footprint is **empty**: the laws moved from the trusted base
//! into the theorem's own hypotheses, which is where they belong. Nothing is
//! lost, because applying the generalized theorem to the 30 `Real` constants
//! (and to the variable/hypothesis axioms) recovers the original `False`
//! verbatim — [`OrderedRingRefutation::instantiated`] is that recovery,
//! admitted through the same trusted gate, with the original footprint back.
//!
//! ## What this is not
//!
//! It does not reduce `real: axiom=30`; the prelude still declares them, and
//! any consumer that wants a `Real`-specific conclusion still instantiates at
//! them. The point is that the *refutation* no longer depends on them: the
//! generalized theorem is the object worth shipping, and it assumes nothing.
//!
//! Nor does it touch the kernel. This is exactly the "parameterise the
//! consumers over the ordered-ring interface" route ADR-0456 named as the one
//! that eliminates the 30 without constructing a carrier.

use std::collections::HashMap;

use axeyum_lean_kernel::{
    BinderInfo, Declaration, ExprId, ExprNode, Kernel, NameId, build_int_model_of_arith,
};

use axeyum_ir::{TermArena, TermId};

use super::{LraReconstructCtx, ReconstructError, reconstruct_lra_proof};

/// The binder name each of the 30 `Real` declarations takes in the generalized
/// statement, in **declaration order** — which is also dependency order, so
/// each binder's type mentions only binders to its left.
///
/// The first eight are the carrier and its operations; the remaining 22 are the
/// ordered-commutative-ring laws.
const RING_BINDER_NAMES: [&str; 30] = [
    "R",
    "add",
    "mul",
    "neg",
    "zero",
    "one",
    "le",
    "lt",
    "le_refl",
    "le_trans",
    "lt_irrefl",
    "lt_trans",
    "lt_of_lt_of_le",
    "lt_of_le_of_lt",
    "le_of_lt",
    "add_le_add",
    "add_comm",
    "add_assoc",
    "add_zero",
    "add_neg",
    "mul_le_mul_of_nonneg_left",
    "zero_lt_one",
    "add_lt_add_of_le_of_lt",
    "mul_comm",
    "mul_assoc",
    "mul_one",
    "mul_zero",
    "left_distrib",
    "mul_nonneg",
    "sq_nonneg",
];

/// How many of the 30 ring binders are the carrier and its operations (the
/// rest are laws).
pub const RING_SYMBOL_BINDERS: usize = 8;

/// The number of ordered-commutative-ring laws the generalized statement takes
/// as hypotheses.
pub const RING_LAW_BINDERS: usize = RING_BINDER_NAMES.len() - RING_SYMBOL_BINDERS;

/// Which part of the `Real` package the generalized statement quantifies over.
///
/// Both scopes produce an axiom-free theorem; they differ in what the reader is
/// promised and in what the instantiation costs.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RingTelescope {
    /// Bind **all 30** — the uniform ordered-commutative-ring interface, the
    /// same statement shape for every refutation regardless of which laws its
    /// proof happens to invoke. This is the form ADR-0456 named. Instantiating
    /// it mentions all 30 `Real` constants, so the recovered theorem's
    /// footprint is a *superset* of the original's: the extra names are the
    /// laws supplied and never used.
    FullInterface,
    /// Bind only the declarations the refutation actually rests on. The
    /// resulting theorem is strictly stronger (fewer hypotheses), and its
    /// instantiation reproduces the original footprint **exactly**, which is
    /// the crispest available demonstration that nothing was lost.
    Used,
}

/// A refutation parameterised over the ordered-ring interface, together with
/// the instantiation that recovers the original `Real`-specific statement.
///
/// Every field is **measured** from the kernel after admission, not asserted by
/// the code that built it.
#[derive(Debug, Clone)]
pub struct OrderedRingRefutation {
    /// Which part of the `Real` package was abstracted.
    pub scope: RingTelescope,
    /// The admitted generalized theorem.
    pub theorem: NameId,
    /// Its proof term: the λ-telescope over the ring interface, the variables,
    /// and the constraint hypotheses.
    pub term: ExprId,
    /// Its type, as the kernel inferred it — the ∀-telescope ending in `False`.
    pub statement: ExprId,
    /// `Kernel::axiom_footprint` of [`Self::theorem`], rendered. **Empty** on
    /// every successful return; a non-empty footprint is an error, not a
    /// result, because the whole point of the construction is that there is
    /// nothing left to depend on.
    pub footprint: Vec<String>,
    /// How many of the 30 `Real` declarations the statement abstracts (30 under
    /// [`RingTelescope::FullInterface`]).
    pub ring_binders: usize,
    /// The `Real` declarations the original refutation actually rests on,
    /// rendered — the honest answer to "which of the 30 does this route still
    /// use". Under [`RingTelescope::Used`] this is exactly what was abstracted.
    pub ring_used: Vec<String>,
    /// How many `R`-typed variable binders the statement carries (one per real
    /// variable the refutation mentions).
    pub var_binders: usize,
    /// How many constraint-hypothesis binders the statement carries (one per
    /// asserted atom the refutation uses).
    pub hyp_binders: usize,
    /// The `Real`-specific theorem recovered by applying [`Self::theorem`] to
    /// the 30 prelude constants and the refutation's own variable/hypothesis
    /// axioms. Its type is `False`, and the kernel re-checked the application.
    pub instantiated: NameId,
    /// `Kernel::axiom_footprint` of [`Self::instantiated`], rendered: the
    /// original statement's trusted base, back in full. This is the evidence
    /// that the generalization is a *strengthening* rather than a different
    /// claim.
    pub instantiated_footprint: Vec<String>,
    /// The original (un-generalized) refutation, admitted as a theorem so its
    /// footprint can be compared against [`Self::instantiated_footprint`].
    pub original: NameId,
    /// `Kernel::axiom_footprint` of [`Self::original`], rendered.
    pub original_footprint: Vec<String>,
    /// The abstracted ring declarations, **in application order** — the
    /// arguments [`Self::theorem`] expects *before* its variable and hypothesis
    /// binders, and only those.
    ///
    /// Deliberately not the whole abstraction telescope: that also carries one
    /// entry per variable and per asserted constraint, which no model of the
    /// ring laws interprets. Getting this wrong is caught rather than papered
    /// over — [`instantiate_at_int_model`] refused with "the refutation
    /// abstracts `axeyum.reconstruct.lra.x.0`, which the integer model does not
    /// interpret".
    ///
    /// Exposed so a consumer can instantiate at a model other than `Real`. That
    /// is the whole point of generalizing: [`instantiate_at_int_model`] supplies
    /// `ℤ` instead, and nothing about the construction is `Real`-specific.
    pub ring_names: Vec<NameId>,
}

impl OrderedRingRefutation {
    /// The total binder count of the generalized statement.
    #[must_use]
    pub fn binder_count(&self) -> usize {
        self.ring_binders + self.var_binders + self.hyp_binders
    }

    /// Whether the instantiation recovered the original statement's trusted
    /// base — the check that nothing was lost.
    ///
    /// A superset rather than equality under
    /// [`RingTelescope::FullInterface`], where the instantiation deliberately
    /// mentions ring laws the proof never used; see
    /// [`Self::instantiation_footprint_is_exact`].
    #[must_use]
    pub fn instantiation_recovers_original(&self) -> bool {
        self.original_footprint
            .iter()
            .all(|name| self.instantiated_footprint.contains(name))
    }

    /// Whether the instantiation's footprint is *identical* to the original's —
    /// true under [`RingTelescope::Used`].
    #[must_use]
    pub fn instantiation_footprint_is_exact(&self) -> bool {
        self.instantiated_footprint == self.original_footprint
    }
}

/// Generalize a kernel-checked LRA/Farkas refutation over the ordered-ring
/// interface, admit it, and admit its instantiation at `Real`.
///
/// `proof` must be a term this `ctx` built (so its constants live in this
/// kernel) whose inferred type is the prelude's `False` — i.e. exactly what
/// [`reconstruct_lra_proof`](super::reconstruct_lra_proof) or
/// [`reconstruct_sos_proof`](super::reconstruct_sos_proof) returns.
///
/// # Errors
///
/// Returns [`ReconstructError::KernelRejected`] if the kernel declines the
/// generalized term or its instantiation, if `proof` does not infer to `False`,
/// if it rests on a trusted declaration outside the abstracted telescope (which
/// would leave a non-empty footprint), or if the measured footprint of the
/// generalized theorem is not empty.
// One linear pipeline -- admit, measure, abstract, admit, instantiate, measure
// -- where each step consumes the previous step's output and the ORDER is the
// argument. Splitting it would move the reasoning into call sites without
// making any part independently testable.
#[allow(clippy::too_many_lines)]
pub fn generalize_over_ordered_ring(
    ctx: &mut LraReconstructCtx,
    proof: ExprId,
    scope: RingTelescope,
) -> Result<OrderedRingRefutation, ReconstructError> {
    // (0) Pin the input: `proof : False`, admitted as a theorem so its footprint
    //     is measurable by name. This is also the baseline the instantiation is
    //     compared against.
    let false_ty = {
        let f = ctx.arith.logic.false_;
        ctx.kernel.const_(f, vec![])
    };
    let original = ctx.fresh_name("refutation");
    ctx.kernel
        .add_declaration(Declaration::Theorem {
            name: original,
            uparams: vec![],
            ty: false_ty,
            value: proof,
        })
        .map_err(|e| ReconstructError::KernelRejected {
            rule: "ordered_ring".to_owned(),
            detail: format!("the refutation is not a proof of False: {e:?}"),
        })?;
    let original_footprint = footprint(&ctx.kernel, original);

    // (1) The abstraction telescope, in dependency order: the ring interface,
    //     then one binder per real variable, then one per constraint hypothesis.
    //     Variables and hypotheses are filtered to those the refutation actually
    //     rests on, so the statement carries no dead binder; the 30 ring binders
    //     are kept unconditionally, because the interface is the point.
    let used: std::collections::BTreeSet<NameId> =
        ctx.kernel.axiom_footprint(original).into_iter().collect();
    let all_ring = ring_telescope(&ctx.arith);
    let ring_used: Vec<String> = all_ring
        .iter()
        .filter(|n| used.contains(n))
        .map(|&n| ctx.kernel.display_name(n).to_string())
        .collect();
    // Each ring entry carries its binder name from here on, so the name never
    // has to be looked up by searching for the entry again.
    let ring: Vec<(NameId, &'static str)> = all_ring
        .iter()
        .copied()
        .zip(RING_BINDER_NAMES)
        .filter(|(name, _)| match scope {
            RingTelescope::FullInterface => true,
            RingTelescope::Used => used.contains(name),
        })
        .collect();
    let vars: Vec<NameId> = ctx
        .vars
        .values()
        .copied()
        .filter(|n| used.contains(n))
        .collect();
    let hyps: Vec<NameId> = ctx
        .hyps
        .iter()
        .copied()
        .filter(|n| used.contains(n))
        .collect();

    // (2) Nothing outside the telescope may remain trusted, or the generalized
    //     theorem cannot be axiom-free. Refuse rather than discover it later:
    //     an unexplained axiom here is a real finding about the route, not a
    //     nuisance.
    let telescope: Vec<NameId> = ring
        .iter()
        .map(|&(name, _)| name)
        .chain(vars.iter().copied())
        .chain(hyps.iter().copied())
        .collect();
    let known: std::collections::BTreeSet<NameId> = telescope.iter().copied().collect();
    let stray: Vec<String> = used
        .iter()
        .filter(|n| !known.contains(n))
        .map(|&n| ctx.kernel.display_name(n).to_string())
        .collect();
    if !stray.is_empty() {
        return Err(ReconstructError::KernelRejected {
            rule: "ordered_ring".to_owned(),
            detail: format!(
                "refutation rests on {} trusted declaration(s) outside the ordered-ring \
                 telescope, so abstracting it cannot be axiom-free: {}",
                stray.len(),
                stray.join(", ")
            ),
        });
    }

    // (3) Binder names, purely cosmetic, but deterministic. A ring binder keeps
    //     the leaf of the declaration it stands for (`Real.add_comm` ↦
    //     `add_comm`), so a rendered statement is readable next to the prelude.
    let mut binder_names: Vec<String> = ring.iter().map(|&(_, binder)| binder.to_owned()).collect();
    for i in 0..vars.len() {
        binder_names.push(format!("x{i}"));
    }
    for i in 0..hyps.len() {
        binder_names.push(format!("h{i}"));
    }

    // (4) Abstract. Each binder's type is the declaration's type in the
    //     environment with every EARLIER telescope entry replaced by its bound
    //     variable — computed from the environment, never written by hand, so a
    //     changed axiom changes the hypothesis rather than silently disagreeing
    //     with it.
    let mut binder_types = Vec::with_capacity(telescope.len());
    for (position, &name) in telescope.iter().enumerate() {
        let declared = ctx
            .kernel
            .environment()
            .get(name)
            .map(Declaration::ty)
            .ok_or_else(|| ReconstructError::KernelRejected {
                rule: "ordered_ring".to_owned(),
                detail: format!(
                    "telescope entry `{}` is not in the environment",
                    ctx.kernel.display_name(name)
                ),
            })?;
        let abstracted = abstract_consts(&mut ctx.kernel, declared, &telescope[..position]);
        binder_types.push(abstracted);
    }
    let body = abstract_consts(&mut ctx.kernel, proof, &telescope);

    // (5) Wrap innermost-out.
    let mut term = body;
    for position in (0..telescope.len()).rev() {
        let anon = ctx.kernel.anon();
        let binder = ctx.kernel.name_str(anon, binder_names[position].clone());
        term = ctx
            .kernel
            .lam(binder, binder_types[position], term, BinderInfo::Default);
    }

    // (6) The kernel computes the statement; we do not state it.
    let statement = ctx
        .kernel
        .infer(term)
        .map_err(|e| ReconstructError::KernelRejected {
            rule: "ordered_ring".to_owned(),
            detail: format!("generalized refutation does not infer: {e:?}"),
        })?;
    let theorem = ctx.fresh_name("ordered_ring_refutation");
    ctx.kernel
        .add_declaration(Declaration::Theorem {
            name: theorem,
            uparams: vec![],
            ty: statement,
            value: term,
        })
        .map_err(|e| ReconstructError::KernelRejected {
            rule: "ordered_ring".to_owned(),
            detail: format!("generalized refutation did not admit: {e:?}"),
        })?;
    let measured = footprint(&ctx.kernel, theorem);
    if !measured.is_empty() {
        return Err(ReconstructError::KernelRejected {
            rule: "ordered_ring".to_owned(),
            detail: format!(
                "generalized refutation still rests on {} axiom(s): {}",
                measured.len(),
                measured.join(", ")
            ),
        });
    }

    // (7) Instantiate at `Real` and recover the original statement. The kernel
    //     re-checks the application against `False`; if the generalization had
    //     weakened or shifted the claim, this is where it would fail.
    let mut applied = ctx.kernel.const_(theorem, vec![]);
    for &name in &telescope {
        let argument = ctx.kernel.const_(name, vec![]);
        applied = ctx.kernel.app(applied, argument);
    }
    let false_ty = {
        let f = ctx.arith.logic.false_;
        ctx.kernel.const_(f, vec![])
    };
    let instantiated = ctx.fresh_name("instantiated_at_real");
    ctx.kernel
        .add_declaration(Declaration::Theorem {
            name: instantiated,
            uparams: vec![],
            ty: false_ty,
            value: applied,
        })
        .map_err(|e| ReconstructError::KernelRejected {
            rule: "ordered_ring".to_owned(),
            detail: format!(
                "instantiating the generalized refutation at Real did not recover False: {e:?}"
            ),
        })?;
    let instantiated_footprint = footprint(&ctx.kernel, instantiated);

    Ok(OrderedRingRefutation {
        scope,
        ring_names: ring.iter().map(|&(name, _)| name).collect(),
        theorem,
        term,
        statement,
        footprint: measured,
        ring_binders: ring.len(),
        ring_used,
        var_binders: vars.len(),
        hyp_binders: hyps.len(),
        instantiated,
        instantiated_footprint,
        original,
        original_footprint,
    })
}

/// Render the generalized refutation as a **self-contained Lean module**.
///
/// The module contains the logical prelude's inductives (`False`, `Eq`) and
/// `Not`, the theorem, and its `#print axioms` audit — and, unlike every other
/// arithmetic module this repository emits, **no `axiom` declaration at all**.
/// Real Lean's own `#print axioms` therefore answers the same question
/// [`Kernel::axiom_footprint`] does, from a kernel that shares no code with
/// ours.
///
/// `refutation` must have been produced by
/// [`generalize_over_ordered_ring`] on `ctx`.
#[must_use]
pub fn render_ordered_ring_module(
    ctx: &LraReconstructCtx,
    refutation: &OrderedRingRefutation,
) -> String {
    ctx.kernel.render_lean_module(
        "axeyum_ordered_ring_refutation",
        refutation.statement,
        refutation.term,
    )
}

/// The 30 `Real` declarations in declaration (= dependency) order.
/// The same refutation, as a theorem about the **integers**.
///
/// [`generalize_over_ordered_ring`] abstracts a `Real` Farkas refutation over
/// the 22 laws of an ordered commutative ring, leaving an axiom-free theorem
/// that holds in *any* model of those laws. `Real` is then one instantiation of
/// it. So is `ℤ`: `build_int_model_of_arith` exhibits the integers as a model of
/// all 22, every witness with an **empty** axiom footprint.
///
/// This applies the generalized theorem to that model and stops there — the ring
/// interface is supplied, the variable and hypothesis binders are left bound. So
/// the result is not `False`; it is
///
/// ```text
/// ∀ (x₀ … x_{n-1} : Int), <the constraints, over Int> → False
/// ```
///
/// which is the refutation restated over `ℤ`. Nothing is relaxed and no
/// embedding is involved: a Farkas combination uses only ring operations and
/// order, never division, which is exactly why the abstraction was possible.
///
/// # Why this is worth having
///
/// A conjunctive integer system whose rational relaxation is already infeasible
/// —  `x > 5 ∧ x < 3`, or `x - y ≤ 1 ∧ y - x ≤ -3` — has an ordinary Farkas
/// refutation, but measured 2026-08-17 every such query routed to `ArithDpll`
/// and rendered a structural attestation: an `axiom P` / `axiom ¬P` shim
/// containing none of the reasoning. The proof existed; only a `Real`-shaped
/// destination for it did.
///
/// # Errors
///
/// [`ReconstructError::KernelRejected`] if the model cannot be built, if a name
/// the refutation abstracted has no interpretation in it, or if the kernel
/// refuses the application — which is where a mismatch between the abstracted
/// telescope and the model's coverage would surface, rather than being papered
/// over.
pub fn instantiate_at_int_model(
    ctx: &mut LraReconstructCtx,
    refutation: &OrderedRingRefutation,
) -> Result<IntInstantiation, ReconstructError> {
    let model = build_int_model_of_arith(&mut ctx.kernel).map_err(|e| {
        ReconstructError::KernelRejected {
            rule: "instantiate_at_int".to_owned(),
            detail: format!("the integer model of the ordered ring did not build: {e:?}"),
        }
    })?;

    // `Real` name -> what `ℤ` supplies for it: the interpreted symbol for the
    // eight carrier/operation constants, the checked witness for each law.
    let mut interpretation: HashMap<NameId, NameId> = HashMap::new();
    for &(real, int) in &model.symbols {
        interpretation.insert(real, int);
    }
    for law in &model.laws {
        interpretation.insert(law.real, law.witness);
    }

    let mut applied = ctx.kernel.const_(refutation.theorem, vec![]);
    for &name in &refutation.ring_names {
        let Some(&replacement) = interpretation.get(&name) else {
            // Not a failure to route around: the telescope abstracted something
            // the model does not interpret, so `ℤ` has not been shown to satisfy
            // it and the instantiation would be unjustified.
            return Err(ReconstructError::KernelRejected {
                rule: "instantiate_at_int".to_owned(),
                detail: format!(
                    "the refutation abstracts `{}`, which the integer model does not interpret",
                    ctx.kernel.display_name(name)
                ),
            });
        };
        let argument = ctx.kernel.const_(replacement, vec![]);
        applied = ctx.kernel.app(applied, argument);
    }

    // The kernel computes the statement; we do not state it. A wrong argument
    // order or a mis-mapped law fails here.
    let statement = ctx
        .kernel
        .infer(applied)
        .map_err(|e| ReconstructError::KernelRejected {
            rule: "instantiate_at_int".to_owned(),
            detail: format!("the integer instantiation does not infer: {e:?}"),
        })?;
    let theorem = ctx.fresh_name("instantiated_at_int");
    ctx.kernel
        .add_declaration(Declaration::Theorem {
            name: theorem,
            uparams: vec![],
            ty: statement,
            value: applied,
        })
        .map_err(|e| ReconstructError::KernelRejected {
            rule: "instantiate_at_int".to_owned(),
            detail: format!("the integer instantiation did not admit: {e:?}"),
        })?;

    let axiom_footprint = footprint(&ctx.kernel, theorem);
    Ok(IntInstantiation {
        theorem,
        statement,
        axiom_footprint,
        laws_modelled: model.laws.len(),
        symbols_interpreted: model.symbols.len(),
        var_binders_hint: refutation.var_binders,
    })
}

/// Discharge an [`IntInstantiation`]'s binders against fresh integer axioms,
/// producing a kernel-checked `False`.
///
/// [`instantiate_at_int_model`] stops at a ∀-statement — the refutation restated
/// over `ℤ`, still waiting for variables and constraints. A Lean *module* needs
/// a closed `False`, so this supplies them: one opaque `Int` axiom per variable
/// binder and one hypothesis axiom per constraint binder, then applies.
///
/// The hypothesis types are **read off the statement**, not rebuilt. Peeling a
/// binder and substituting the fresh constant leaves exactly the type the
/// theorem expects next, so there is no second normalization that could disagree
/// with the first — the failure mode where a sound certificate is rejected
/// because the consumer encoded the same constraint differently.
///
/// The declared hypotheses ARE the query's constraints, in the normalized form
/// the refutation uses. That is the same bar the `Real` LRA modules meet, where
/// the rendered hypothesis axioms are likewise normalized rather than verbatim
/// source syntax.
///
/// # Errors
///
/// [`ReconstructError::KernelRejected`] if a binder cannot be discharged or the
/// application does not infer `False` — which is where a mis-peeled telescope
/// would surface rather than producing a module about the wrong constraints.
pub fn refutation_over_int_axioms(
    ctx: &mut LraReconstructCtx,
    instantiation: &IntInstantiation,
) -> Result<IntRefutation, ReconstructError> {
    let mut ty = instantiation.statement;
    let mut arguments: Vec<ExprId> = Vec::new();
    let mut variables: Vec<NameId> = Vec::new();
    let mut hypotheses: Vec<NameId> = Vec::new();

    // Peel every binder, declaring what it asks for. A variable binder wants an
    // inhabitant of `Int`; a constraint binder wants a proof of a Prop. Both are
    // supplied as axioms — they are the query's own data, exactly as the `Real`
    // route treats its variables and assertions.
    while let ExprNode::Pi(_, domain, body, _) = *ctx.kernel.expr_node(ty) {
        let is_variable = variables.len() < instantiation.var_binders_hint;
        let name = if is_variable {
            ctx.fresh_name("int_var")
        } else {
            ctx.fresh_name("int_hyp")
        };
        ctx.kernel
            .add_declaration(Declaration::Axiom {
                name,
                uparams: vec![],
                ty: domain,
            })
            .map_err(|e| ReconstructError::KernelRejected {
                rule: "int_axioms".to_owned(),
                detail: format!("could not declare a binder's axiom: {e:?}"),
            })?;
        let constant = ctx.kernel.const_(name, vec![]);
        arguments.push(constant);
        if is_variable {
            variables.push(name);
        } else {
            hypotheses.push(name);
        }
        ty = ctx.kernel.instantiate(body, &[constant]);
    }

    let mut applied = ctx.kernel.const_(instantiation.theorem, vec![]);
    for argument in &arguments {
        applied = ctx.kernel.app(applied, *argument);
    }
    let inferred = ctx
        .kernel
        .infer(applied)
        .map_err(|e| ReconstructError::KernelRejected {
            rule: "int_axioms".to_owned(),
            detail: format!("the discharged integer refutation does not infer: {e:?}"),
        })?;
    let false_ = {
        let f = ctx.arith.logic.false_;
        ctx.kernel.const_(f, vec![])
    };
    if !ctx.kernel.def_eq(inferred, false_) {
        return Err(ReconstructError::KernelRejected {
            rule: "int_axioms".to_owned(),
            detail: "discharging every binder did not leave False; the statement's telescope is \
                     not what this route assumed"
                .to_owned(),
        });
    }

    Ok(IntRefutation {
        proof: applied,
        variables,
        hypotheses,
    })
}

/// Reconstruct an INTEGER linear refutation to a self-contained Lean module.
///
/// The whole pipeline, for a conjunctive integer system whose rational
/// relaxation is already infeasible:
///
/// 1. relax `Int` to `Real` faithfully (fresh symbols, injective map),
/// 2. refute the relaxation by Farkas — [`reconstruct_lra_proof`],
/// 3. abstract that proof over the 22 ordered-ring laws — axiom-free,
/// 4. instantiate at `ℤ`, which models all 22 with empty footprints,
/// 5. discharge the binders against the query's own integer variables and
///    constraints, giving `False`,
/// 6. render.
///
/// No step relaxes the CLAIM. The relaxation is used only to find the Farkas
/// combination; the combination is then carried out in `ℤ` itself, because it
/// uses ring operations and order and never division. What comes back is a
/// theorem about the integers, not about their real embedding.
///
/// # Errors
///
/// Declines ([`ReconstructError`]) when the query has no clean real analogue,
/// when the relaxation is not Farkas-refutable (an integer-only infeasibility
/// such as `3x ≥ 1 ∧ 3x ≤ 2` — that is
/// [`crate::int_reconstruct::reconstruct_int_inequality_to_lean_module`]'s job,
/// not this one), or when any kernel step refuses.
pub fn reconstruct_int_farkas_to_lean_module(
    arena: &TermArena,
    assertions: &[TermId],
) -> Result<String, ReconstructError> {
    let relaxed =
        crate::int_real_relax::relax_int_assertions_to_real(arena, assertions).map_err(|e| {
            ReconstructError::KernelRejected {
                rule: "int_farkas".to_owned(),
                detail: format!("the real relaxation failed: {e}"),
            }
        })?;
    let Some((scratch, relaxed_assertions)) = relaxed else {
        return Err(ReconstructError::UnsupportedRule {
            rule: "int_farkas: the query has no faithful real relaxation".to_owned(),
        });
    };

    let mut ctx = LraReconstructCtx::new();
    let proof = reconstruct_lra_proof(&mut ctx, &scratch, &relaxed_assertions)?;
    let generalized = generalize_over_ordered_ring(&mut ctx, proof, RingTelescope::FullInterface)?;
    let at_int = instantiate_at_int_model(&mut ctx, &generalized)?;
    let closed = refutation_over_int_axioms(&mut ctx, &at_int)?;

    let false_ = {
        let logic_false = ctx.arith.logic.false_;
        ctx.kernel.const_(logic_false, vec![])
    };
    Ok(ctx
        .kernel
        .render_lean_module("axeyum_refutation", false_, closed.proof))
}

/// A closed integer refutation: `False`, from declared integer axioms.
#[derive(Debug, Clone)]
pub struct IntRefutation {
    /// The proof term, of type `False`.
    pub proof: ExprId,
    /// The opaque `Int` axioms standing for the query's variables.
    pub variables: Vec<NameId>,
    /// The hypothesis axioms standing for its constraints, in binder order.
    pub hypotheses: Vec<NameId>,
}

/// A generalized refutation, instantiated at the integers.
#[derive(Debug, Clone)]
pub struct IntInstantiation {
    /// The admitted theorem: the refutation's constraints over `Int` imply
    /// `False`.
    pub theorem: NameId,
    /// Its type, as the kernel inferred it.
    pub statement: ExprId,
    /// `Kernel::axiom_footprint` of [`Self::theorem`], rendered.
    ///
    /// **Expected to be empty.** The generalized theorem is axiom-free, and
    /// every law witness the integer model supplies has an empty footprint too,
    /// so the composite rests on nothing. A non-empty footprint here is a
    /// finding, not a formality: it means `ℤ` is carrying an assumption.
    pub axiom_footprint: Vec<String>,
    /// How many laws the model discharged (22 for the ordered-ring interface).
    pub laws_modelled: usize,
    /// How many carrier/operation symbols it interpreted (8).
    pub symbols_interpreted: usize,
    /// How many of the statement's leading binders are VARIABLES rather than
    /// constraints — carried from the generalization, because the two are both
    /// `Pi` nodes and telling them apart by inspecting types would be a guess.
    pub var_binders_hint: usize,
}

fn ring_telescope(arith: &axeyum_lean_kernel::ArithPrelude) -> [NameId; 30] {
    [
        arith.r,
        arith.add,
        arith.mul,
        arith.neg,
        arith.zero,
        arith.one,
        arith.le,
        arith.lt,
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
    ]
}

/// `Kernel::axiom_footprint`, rendered and sorted (the kernel already sorts by
/// rendered name).
fn footprint(kernel: &Kernel, name: NameId) -> Vec<String> {
    kernel
        .axiom_footprint(name)
        .into_iter()
        .map(|n| kernel.display_name(n).to_string())
        .collect()
}

/// Replace every `Const` in `order` by the bound variable of the binder that
/// will stand for it: `order[j]` becomes `BVar(order.len() - 1 - j)` at the
/// outermost level, shifted by the number of binders crossed.
///
/// The dual of [`Kernel::abstract_fvars`], which does the same job for free
/// variables. Constants are what a proof term over a prelude actually mentions,
/// so this is the operation that turns "a theorem about `Real`" into "a theorem
/// about any structure with these operations".
///
/// Universe arguments, binder names and binder info ride through untouched, so
/// the abstracted axiom type is the axiom, not a restatement of it — the same
/// discipline `build_int_model_of_arith` uses for its interpretation.
fn abstract_consts(kernel: &mut Kernel, e: ExprId, order: &[NameId]) -> ExprId {
    if order.is_empty() {
        return e;
    }
    let indices: HashMap<NameId, u32> = order
        .iter()
        .enumerate()
        .map(|(j, &name)| {
            (
                name,
                u32::try_from(order.len() - 1 - j).expect("telescope length fits u32"),
            )
        })
        .collect();
    let mut memo = HashMap::new();
    abstract_consts_aux(kernel, e, &indices, 0, &mut memo)
}

fn abstract_consts_aux(
    kernel: &mut Kernel,
    e: ExprId,
    indices: &HashMap<NameId, u32>,
    offset: u32,
    memo: &mut HashMap<(ExprId, u32), ExprId>,
) -> ExprId {
    if let Some(&hit) = memo.get(&(e, offset)) {
        return hit;
    }
    let rebuilt = match kernel.expr_node(e).clone() {
        ExprNode::BVar(_) | ExprNode::FVar(_) | ExprNode::Sort(_) | ExprNode::Lit(_) => e,
        ExprNode::Const(name, _) => match indices.get(&name) {
            Some(&index) => kernel.bvar(index + offset),
            None => e,
        },
        ExprNode::Proj(ty, field, structure) => {
            let structure = abstract_consts_aux(kernel, structure, indices, offset, memo);
            kernel.proj(ty, field, structure)
        }
        ExprNode::App(fun, arg) => {
            let fun = abstract_consts_aux(kernel, fun, indices, offset, memo);
            let arg = abstract_consts_aux(kernel, arg, indices, offset, memo);
            kernel.app(fun, arg)
        }
        ExprNode::Lam(name, ty, body, info) => {
            let ty = abstract_consts_aux(kernel, ty, indices, offset, memo);
            let body = abstract_consts_aux(kernel, body, indices, offset + 1, memo);
            kernel.lam(name, ty, body, info)
        }
        ExprNode::Pi(name, ty, body, info) => {
            let ty = abstract_consts_aux(kernel, ty, indices, offset, memo);
            let body = abstract_consts_aux(kernel, body, indices, offset + 1, memo);
            kernel.pi(name, ty, body, info)
        }
        ExprNode::Let(name, ty, value, body) => {
            let ty = abstract_consts_aux(kernel, ty, indices, offset, memo);
            let value = abstract_consts_aux(kernel, value, indices, offset, memo);
            let body = abstract_consts_aux(kernel, body, indices, offset + 1, memo);
            kernel.let_(name, ty, value, body)
        }
    };
    memo.insert((e, offset), rebuilt);
    rebuilt
}

#[cfg(test)]
mod ordered_ring_tests;
