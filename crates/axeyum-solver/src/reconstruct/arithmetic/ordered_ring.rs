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

use super::{LraReconstructCtx, ReconstructError, RingSignature, reconstruct_lra_proof};

pub(crate) mod setoid;

pub use setoid::{
    EQUALITY_SLOT_BINDERS, EQUALITY_SLOT_LAWS, EqSetoidWitnesses, EqualitySlot, SetoidAdoption,
    SetoidEq,
};

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

/// The binder names of the **setoid** telescope (ADR-0468 phase R3), in
/// declaration order: the same eight carrier/operation symbols, then the nine
/// equality-slot binders, then the same 22 laws — nine of which are now stated
/// through the bound `eq` rather than through the kernel's `Eq`.
///
/// 30 → 39. The symbols keep their positions and the 22 laws keep their relative
/// order, which is what lets
/// [`specialize_setoid_to_eq`] hand the 22 law binders straight through.
const SETOID_RING_BINDER_NAMES: [&str; 39] = [
    "R",
    "add",
    "mul",
    "neg",
    "zero",
    "one",
    "le",
    "lt",
    // --- the equality slot ---
    "eq",
    "eq_refl",
    "eq_symm",
    "eq_trans",
    "add_congr",
    "mul_congr",
    "neg_congr",
    "le_congr",
    "lt_congr",
    // --- the 22 laws ---
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

/// The binder count of the setoid telescope: the 30 of the `Eq`-shaped interface
/// plus the [`EQUALITY_SLOT_BINDERS`] that make equality a parameter.
pub const SETOID_RING_BINDERS: usize = RING_BINDER_NAMES.len() + EQUALITY_SLOT_BINDERS;

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
    /// Bind all 39 of the **setoid** interface (ADR-0468 phase R3): the eight
    /// symbols, an equality *parameter* with its three equivalence laws and five
    /// congruences, and the 22 laws — the nine `Eq`-stated ones restated through
    /// the parameter.
    ///
    /// Requires a proof built with
    /// [`LraReconstructCtx::enable_setoid_equality`]; a proof that used the
    /// kernel's `Eq` still rests on the `Real` package's `Eq`-shaped laws, which
    /// this telescope does not bind, and is refused rather than silently
    /// generalized over the wrong thing.
    ///
    /// This is the form the constructed ℝ can be instantiated at: `CReal`'s
    /// equality is the defined relation `CReal.Equiv`, not `Eq CReal`, and that
    /// is precisely what keeps its trusted surface at zero.
    SetoidInterface,
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
    let (all_ring, binder_table): (Vec<NameId>, &'static [&'static str]) = match scope {
        RingTelescope::SetoidInterface => {
            let Some(slot) = ctx.setoid else {
                return Err(ReconstructError::KernelRejected {
                    rule: "ordered_ring".to_owned(),
                    detail: "the setoid telescope was requested but this context has no equality \
                             slot; call `enable_setoid_equality` BEFORE reconstructing, so the \
                             proof term is built against the parameter rather than against `Eq`"
                        .to_owned(),
                });
            };
            (
                setoid_ring_telescope(&ctx.arith, &slot).to_vec(),
                &SETOID_RING_BINDER_NAMES[..],
            )
        }
        RingTelescope::FullInterface | RingTelescope::Used => {
            (ring_telescope(&ctx.arith).to_vec(), &RING_BINDER_NAMES[..])
        }
    };
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
        .zip(binder_table.iter().copied())
        .filter(|(name, _)| match scope {
            RingTelescope::FullInterface | RingTelescope::SetoidInterface => true,
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
/// 1. relax `Int` to `Real` faithfully (fresh symbols, injective map) — the
///    relaxation is a *search* device, used to find the Farkas combination,
/// 2. refute it by Farkas directly **in a context over the constructed
///    integers** ([`LraReconstructCtx::try_new_over_integers`]),
/// 3. render.
///
/// No step relaxes the CLAIM. The combination is carried out in `ℤ` itself,
/// because it uses ring operations and order and never division. What comes
/// back is a theorem about the integers, not about their real embedding.
///
/// # Why this no longer goes through the `Real` package
///
/// Until 2026-08-18 this route built [`LraReconstructCtx::new`] — the
/// axiomatized `Real` package, this repository's entire remaining trusted
/// surface — refuted there, abstracted the proof over the 22 ordered-ring laws
/// with [`generalize_over_ordered_ring`], and instantiated the result at `ℤ`
/// through [`instantiate_at_int_model`]. The finished term named no `Real`
/// axiom, so the emitted module was already clean; but the route *constructed*
/// 30 axioms to produce it, and it was the **only shipped route that still
/// did** — `prove_unsat_to_lean_module`'s other arithmetic fragments moved to
/// `CReal` in `a6ee37c6a`, and this one was missed because
/// `examples/front_door_carrier.rs` had no integer fixture to measure it with.
///
/// `ℤ` satisfies the same interface with all 30 declarations *proved*
/// (`RingSignature: From<IntPrelude>`), so the abstract-then-instantiate
/// detour buys nothing here: refuting in the integer context lands on the same
/// statement without the intermediate assumptions. Those two functions remain
/// public — the ℤ-model result they carry is worth having — but nothing
/// shipped calls them.
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

    let mut ctx = LraReconstructCtx::try_new_over_integers()?;
    let proof = reconstruct_lra_proof(&mut ctx, &scratch, &relaxed_assertions)?;

    let false_ = {
        let logic_false = ctx.arith.logic.false_;
        ctx.kernel.const_(logic_false, vec![])
    };
    Ok(ctx
        .kernel
        .render_lean_module("axeyum_refutation", false_, proof))
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

/// The 39 declarations of the **setoid** interface, in dependency order: the
/// eight symbols, the equality slot, then the 22 laws with the nine `Eq`-stated
/// ones replaced by their restatements through `eq`.
///
/// Positionally aligned with [`SETOID_RING_BINDER_NAMES`], and — outside the
/// equality slot — with [`ring_telescope`], which is what makes the round trip
/// through `Eq` a straight positional hand-off.
fn setoid_ring_telescope(arith: &RingSignature, slot: &SetoidEq) -> [NameId; 39] {
    [
        arith.r,
        arith.add,
        arith.mul,
        arith.neg,
        arith.zero,
        arith.one,
        arith.le,
        arith.lt,
        slot.eq,
        slot.eq_refl,
        slot.eq_symm,
        slot.eq_trans,
        slot.add_congr,
        slot.mul_congr,
        slot.neg_congr,
        slot.le_congr,
        slot.lt_congr,
        arith.le_refl,
        arith.le_trans,
        arith.lt_irrefl,
        arith.lt_trans,
        arith.lt_of_lt_of_le,
        arith.lt_of_le_of_lt,
        arith.le_of_lt,
        arith.add_le_add,
        slot.add_comm,
        slot.add_assoc,
        slot.add_zero,
        slot.add_neg,
        arith.mul_le_mul_of_nonneg_left,
        arith.zero_lt_one,
        arith.add_lt_add_of_le_of_lt,
        slot.mul_comm,
        slot.mul_assoc,
        slot.mul_one,
        slot.mul_zero,
        slot.left_distrib,
        arith.mul_nonneg,
        arith.sq_nonneg,
    ]
}

/// The 30-entry ring prefix of the abstraction telescope, in the declaration
/// order [`RING_BINDER_NAMES`] names.
///
/// Read off the signature rather than written out again here: the two lists have
/// to agree entry for entry, and one of them is enough.
fn ring_telescope(arith: &RingSignature) -> [NameId; 30] {
    arith.declarations()
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

// ---------------------------------------------------------------------------
// The round trip: instantiating the equality slot back at `Eq`.
// ---------------------------------------------------------------------------

/// A setoid-generalized refutation with its equality slot instantiated at the
/// kernel's `Eq`, and the comparison against the `Eq`-shaped generalization of
/// the same query.
///
/// Every field is **measured** after the kernel admitted the specialization; the
/// verdict is an equality of interned expressions, not a rendering heuristic.
#[derive(Debug, Clone)]
pub struct EqSpecialization {
    /// The specialization term: a λ over the 30 `Eq`-shaped binders whose body
    /// applies the 39-binder theorem, filling the equality slot with `Eq` and its
    /// five congruences at the *bound* carrier.
    pub term: ExprId,
    /// Its type, as the kernel inferred it.
    pub statement: ExprId,
    /// The [`RingTelescope::FullInterface`] statement it is compared against.
    pub reference: ExprId,
    /// Whether the specialization reproduced today's statement — both the
    /// **conclusion** ([`Self::statement`] is the same interned expression as
    /// [`Self::reference`]) and every **hypothesis type**
    /// ([`Self::binder_type_mismatches`] is empty).
    ///
    /// Both halves are needed and neither implies the other. The conclusion
    /// alone is weak: this function re-opens the reference's own binders, so
    /// their types are identical by construction and only the ∀-variables /
    /// constraints tail is really being compared. The binder types are where the
    /// nine rewritten laws actually get checked — and they are consumed by the
    /// application, so they leave no trace in the conclusion.
    ///
    /// Expressions are hash-consed, so both halves are structural identity, not
    /// a definitional-equality check that would happily accept a reshaped
    /// statement (a `fun a b => Eq R a b` in place of `Eq R`, say).
    pub reproduces_reference: bool,
    /// The telescope positions whose type the specialization did **not**
    /// reproduce, rendered as `position: expected | got`.
    ///
    /// Compared over the 30 non-slot positions only: the eight symbols and the
    /// 22 laws, nine of which were restated through `eq` and must come back
    /// verbatim when `eq` is instantiated at `Eq R`. The nine equality-slot
    /// positions have no counterpart in the `Eq`-shaped telescope by
    /// construction, and are the whole point of the widening.
    pub binder_type_mismatches: Vec<String>,
    /// How many of the 30 non-slot binder types were reproduced exactly.
    pub binder_types_reproduced: usize,
    /// [`Self::statement`], rendered. Populated so a failure prints the two
    /// statements rather than only a `false`.
    pub statement_rendered: String,
    /// [`Self::reference`], rendered.
    pub reference_rendered: String,
    /// The admitted specialization theorem.
    pub theorem: NameId,
    /// `Kernel::axiom_footprint` of [`Self::theorem`], rendered. **Empty**: the
    /// 39-binder theorem assumes nothing and the five `Eq` witnesses are proved
    /// from `Eq.rec`, so instantiating one at the other cannot introduce an
    /// assumption. A non-empty footprint here is a finding.
    pub footprint: Vec<String>,
    /// The kernel-`Eq` constants the **setoid** proof term still mentions,
    /// rendered. **Empty**, and the reason this field exists is that nothing else
    /// in this module can catch it being non-empty.
    ///
    /// `Eq`, `Eq.refl` and `Eq.rec` are an inductive and its recursor, not
    /// axioms, so a proof step that kept using `Eq.rec` leaves the generalized
    /// theorem's [`Kernel::axiom_footprint`] **empty** and its telescope 39 long
    /// — every other number in this module still reads as a success — while the
    /// theorem has quietly become uninstantiable at a carrier whose equality is a
    /// defined relation, which is the entire purpose of the exercise. So the slot
    /// being *declared* is not evidence the proof went through it; this is.
    pub setoid_residual_eq: Vec<String>,
}

/// Instantiate a setoid-generalized refutation's **equality slot** at the
/// kernel's `Eq`, and check that what comes back is today's `Eq`-shaped
/// statement.
///
/// This is the test ADR-0468 phase R3 names. Widening the interface from 30
/// binders to 39 is only sound as a *generalization* if the 39-binder statement
/// specializes back to the 30-binder one — otherwise the rewrite quietly changed
/// what the theorem proves, and every downstream instantiation (including at the
/// constructed ℝ) would be proving something else.
///
/// The specialization is not an application at `Real`: the carrier stays
/// **bound**. The 30 `Eq`-shaped binders are re-introduced from `reference`'s own
/// statement, and inside them the 39-binder theorem is applied to
///
/// ```text
/// R … lt                       the eight symbols, unchanged
/// Eq R                         the equality parameter
/// Eq.refl R, symm R, trans R   its three equivalence laws
/// congr₂ R add, congr₂ R mul, congr₁ R neg, relCongr R le, relCongr R lt
/// le_refl … sq_nonneg          the 22 laws, unchanged
/// ```
///
/// `Eq R` is supplied as a *partial application*, never as `fun a b => Eq R a b`.
/// That is the detail that makes the result an identity rather than a
/// definitional equality: `eq x y` instantiates to the very node `Eq R x y` that
/// the `Eq`-shaped statement already contains, with no β-redex to reduce and
/// nothing for a normalizer to have to agree about.
///
/// # Errors
///
/// [`ReconstructError::KernelRejected`] if `setoid` is not a
/// [`RingTelescope::SetoidInterface`] refutation, if `reference` is not a
/// [`RingTelescope::FullInterface`] one, if the reference statement does not open
/// into 30 binders, or if the kernel refuses the specialization — which is where
/// a mismatched equality-slot type would surface.
// One linear pipeline -- declare the witnesses, re-open the reference's binders,
// assemble the 39 arguments, close, infer, compare -- where the ORDER is the
// argument and no step is meaningful without its predecessor.
#[allow(clippy::too_many_lines)]
pub fn specialize_setoid_to_eq(
    ctx: &mut LraReconstructCtx,
    setoid: &OrderedRingRefutation,
    reference: &OrderedRingRefutation,
) -> Result<EqSpecialization, ReconstructError> {
    if setoid.scope != RingTelescope::SetoidInterface {
        return Err(ReconstructError::KernelRejected {
            rule: "specialize_at_eq".to_owned(),
            detail: format!(
                "the specialization source must be a setoid generalization, not {:?}",
                setoid.scope
            ),
        });
    }
    if reference.scope != RingTelescope::FullInterface {
        return Err(ReconstructError::KernelRejected {
            rule: "specialize_at_eq".to_owned(),
            detail: format!(
                "the comparison reference must be a full-interface generalization, not {:?}",
                reference.scope
            ),
        });
    }

    // The five generic `Eq`-is-a-setoid lemmas, proved from `Eq.rec`. Minted
    // under a fresh namespace so repeated calls in one context cannot collide.
    let witness_ns = ctx.fresh_name("eq_setoid");
    let logic = ctx.arith.logic;
    let witnesses = setoid::declare_eq_setoid_witnesses(&mut ctx.kernel, &logic, witness_ns)?;

    // Re-open the reference statement's 30 binders as free variables, keeping
    // their names and types. Read off the statement rather than rebuilt, so the
    // λ-telescope this function closes is the reference's own telescope and the
    // comparison cannot pass by accident of a reconstruction that agrees.
    let mut ty = reference.statement;
    let mut fvar_ids: Vec<u64> = Vec::with_capacity(reference.ring_binders);
    let mut fvar_exprs: Vec<ExprId> = Vec::with_capacity(reference.ring_binders);
    let mut binder_tys: Vec<ExprId> = Vec::with_capacity(reference.ring_binders);
    let mut binder_names: Vec<NameId> = Vec::with_capacity(reference.ring_binders);
    for position in 0..reference.ring_binders {
        let ExprNode::Pi(name, domain, body, _) = *ctx.kernel.expr_node(ty) else {
            return Err(ReconstructError::KernelRejected {
                rule: "specialize_at_eq".to_owned(),
                detail: format!(
                    "the reference statement runs out of binders at position {position} of {}",
                    reference.ring_binders
                ),
            });
        };
        let id = ctx.fresh_fvar_id();
        let fvar = ctx.kernel.fvar(id);
        fvar_ids.push(id);
        fvar_exprs.push(fvar);
        binder_tys.push(domain);
        binder_names.push(name);
        ty = ctx.kernel.instantiate(body, &[fvar]);
    }

    // The 39 arguments: eight symbols, the equality slot, 22 laws.
    let carrier = fvar_exprs[0];
    let one_lvl = {
        let z = ctx.kernel.level_zero();
        ctx.kernel.level_succ(z)
    };
    let mut arguments: Vec<ExprId> = fvar_exprs[..RING_SYMBOL_BINDERS].to_vec();
    let eq_at_carrier = {
        let c = ctx.kernel.const_(logic.eq, vec![one_lvl]);
        ctx.kernel.app(c, carrier)
    };
    let refl_at_carrier = {
        let c = ctx.kernel.const_(logic.eq_refl, vec![one_lvl]);
        ctx.kernel.app(c, carrier)
    };
    let at_carrier = |ctx: &mut LraReconstructCtx, name: NameId| {
        let c = ctx.kernel.const_(name, vec![]);
        ctx.kernel.app(c, carrier)
    };
    let at_carrier_and = |ctx: &mut LraReconstructCtx, name: NameId, op: ExprId| {
        let c = ctx.kernel.const_(name, vec![]);
        let e = ctx.kernel.app(c, carrier);
        ctx.kernel.app(e, op)
    };
    // Positions in the eight-symbol prefix: add=1, mul=2, neg=3, le=6, lt=7.
    let (add, mul, neg, le, lt) = (
        fvar_exprs[1],
        fvar_exprs[2],
        fvar_exprs[3],
        fvar_exprs[6],
        fvar_exprs[7],
    );
    arguments.push(eq_at_carrier);
    arguments.push(refl_at_carrier);
    let symm = at_carrier(ctx, witnesses.symm);
    arguments.push(symm);
    let trans = at_carrier(ctx, witnesses.trans);
    arguments.push(trans);
    let add_congr = at_carrier_and(ctx, witnesses.congr2, add);
    arguments.push(add_congr);
    let mul_congr = at_carrier_and(ctx, witnesses.congr2, mul);
    arguments.push(mul_congr);
    let neg_congr = at_carrier_and(ctx, witnesses.congr1, neg);
    arguments.push(neg_congr);
    let le_congr = at_carrier_and(ctx, witnesses.rel_congr, le);
    arguments.push(le_congr);
    let lt_congr = at_carrier_and(ctx, witnesses.rel_congr, lt);
    arguments.push(lt_congr);
    arguments.extend_from_slice(&fvar_exprs[RING_SYMBOL_BINDERS..]);

    if arguments.len() != setoid.ring_binders {
        return Err(ReconstructError::KernelRejected {
            rule: "specialize_at_eq".to_owned(),
            detail: format!(
                "assembled {} arguments for a telescope of {}",
                arguments.len(),
                setoid.ring_binders
            ),
        });
    }

    let mut body = ctx.kernel.const_(setoid.theorem, vec![]);
    for argument in &arguments {
        body = ctx.kernel.app(body, *argument);
    }

    // Close the λ-telescope. `abstract_fvars` owns the index arithmetic,
    // including the shifts inside the equality witnesses' own binders.
    let mut term = ctx.kernel.abstract_fvars(body, &fvar_ids);
    for position in (0..fvar_ids.len()).rev() {
        let domain = ctx
            .kernel
            .abstract_fvars(binder_tys[position], &fvar_ids[..position]);
        term = ctx
            .kernel
            .lam(binder_names[position], domain, term, BinderInfo::Default);
    }

    // Walk the setoid telescope one argument at a time, recording each binder's
    // DOMAIN as the specialization sees it. The 30 non-slot domains must be the
    // reference's own, node for node: that is where the nine restated laws are
    // actually checked, and the application consumes them, so nothing about them
    // survives into the inferred conclusion.
    let mut walked = setoid.statement;
    let mut supplied_domains: Vec<ExprId> = Vec::with_capacity(arguments.len());
    for argument in &arguments {
        let ExprNode::Pi(_, domain, body, _) = *ctx.kernel.expr_node(walked) else {
            return Err(ReconstructError::KernelRejected {
                rule: "specialize_at_eq".to_owned(),
                detail: format!(
                    "the setoid statement runs out of binders after {} of {}",
                    supplied_domains.len(),
                    arguments.len()
                ),
            });
        };
        supplied_domains.push(domain);
        walked = ctx.kernel.instantiate(body, &[*argument]);
    }
    let slot_end = RING_SYMBOL_BINDERS + EQUALITY_SLOT_BINDERS;
    let compared: Vec<(usize, ExprId, ExprId)> = supplied_domains
        .iter()
        .enumerate()
        .filter(|(position, _)| *position < RING_SYMBOL_BINDERS || *position >= slot_end)
        .zip(binder_tys.iter())
        .map(|((position, &got), &expected)| (position, expected, got))
        .collect();
    let mut binder_type_mismatches = Vec::new();
    for &(position, expected, got) in &compared {
        if expected != got {
            let expected = ctx.kernel.render_lean(expected);
            let got = ctx.kernel.render_lean(got);
            binder_type_mismatches.push(format!(
                "{}: {expected} | {got}",
                SETOID_RING_BINDER_NAMES
                    .get(position)
                    .copied()
                    .unwrap_or("?")
            ));
        }
    }
    let binder_types_reproduced = compared.len() - binder_type_mismatches.len();

    let statement = ctx
        .kernel
        .infer(term)
        .map_err(|e| ReconstructError::KernelRejected {
            rule: "specialize_at_eq".to_owned(),
            detail: format!("the specialization at `Eq` does not infer: {e:?}"),
        })?;
    let theorem = ctx.fresh_name("setoid_specialized_at_eq");
    ctx.kernel
        .add_declaration(Declaration::Theorem {
            name: theorem,
            uparams: vec![],
            ty: statement,
            value: term,
        })
        .map_err(|e| ReconstructError::KernelRejected {
            rule: "specialize_at_eq".to_owned(),
            detail: format!("the specialization at `Eq` did not admit: {e:?}"),
        })?;

    Ok(EqSpecialization {
        term,
        statement,
        reference: reference.statement,
        reproduces_reference: statement == reference.statement
            && binder_type_mismatches.is_empty()
            // A vacuous comparison would otherwise report success: if the two
            // telescopes stopped lining up, `zip` would silently compare a
            // prefix.
            && binder_types_reproduced == reference.ring_binders,
        binder_type_mismatches,
        binder_types_reproduced,
        statement_rendered: ctx.kernel.render_lean(statement),
        reference_rendered: ctx.kernel.render_lean(reference.statement),
        theorem,
        footprint: footprint(&ctx.kernel, theorem),
        setoid_residual_eq: residual_eq_constants(ctx, setoid.term),
    })
}

/// The **axiom footprint of a refutation term**, as the kernel computes it.
///
/// Admits `proof` as a `Theorem : False` under a fresh name and returns
/// [`Kernel::axiom_footprint`](axeyum_lean_kernel::Kernel) of it — this kernel's
/// `#print axioms`, transitive through every theorem and definition the proof
/// reaches. Read from the kernel rather than from the rendered module text,
/// because the module renders inductives as `axiom` too and counting those lines
/// would over-report by dozens.
///
/// The footprint of a *shipped* refutation is never empty: the query's own
/// variables and constraints are declared axioms (`axeyum.reconstruct.lra.x.*`,
/// `…hyp.*`) and abstracting them is exactly what
/// [`generalize_over_ordered_ring`] does. What matters is what is left over —
/// see [`carrier_axioms_of`].
///
/// # Errors
///
/// [`ReconstructError::KernelRejected`] if `proof` is not a proof of `False`.
pub fn refutation_axiom_footprint(
    ctx: &mut LraReconstructCtx,
    proof: ExprId,
) -> Result<Vec<String>, ReconstructError> {
    let false_ty = {
        let f = ctx.arith.logic.false_;
        ctx.kernel.const_(f, vec![])
    };
    let name = ctx.fresh_name("front_door_refutation");
    ctx.kernel
        .add_declaration(Declaration::Theorem {
            name,
            uparams: vec![],
            ty: false_ty,
            value: proof,
        })
        .map_err(|e| ReconstructError::KernelRejected {
            rule: "refutation_axiom_footprint".to_owned(),
            detail: format!("the refutation is not a proof of False: {e:?}"),
        })?;
    Ok(footprint(&ctx.kernel, name))
}

/// Is this footprint entry one of the query's OWN free variables or hypotheses?
///
/// Exactly `axeyum.reconstruct.<route>.x.<n>` and
/// `axeyum.reconstruct.<route>.hyp.<n>`. Deliberately narrow: see
/// [`minted_axioms_of`] for why "under the reconstruct namespace" is not the
/// same question.
fn is_query_local(name: &str) -> bool {
    let Some(rest) = name.strip_prefix("axeyum.reconstruct.") else {
        return false;
    };
    let Some((_route, tail)) = rest.rsplit_once('.').and_then(|(head, index)| {
        index.parse::<u64>().ok()?;
        head.rsplit_once('.')
    }) else {
        return false;
    };
    tail == "x" || tail == "hyp"
}

/// Axioms this route MINTED for the query that are not the query's own
/// variables or hypotheses.
///
/// This exists because "outside the `axeyum.reconstruct.` namespace" is a
/// weaker question than it looks, and [`carrier_axioms_of`] alone was answering
/// the weaker one. That namespace is not reserved for query variables: the
/// `Real` route mints its **eighteen equality-slot axioms** there, the
/// Ackermann route mints `axeyum.reconstruct.func._*`, and `.dio`, `.word`,
/// `.lex` and `.regex` all mint under it too. An assumption minted there is
/// still an assumption; excluding it by prefix would let a route buy a
/// zero-carrier-axiom result by minting what it needs under its own name.
///
/// So the honest claim about a refutation is that **both** this and
/// [`carrier_axioms_of`] are empty. Over the constructed reals both are, because
/// `adopt_setoid_equality` takes the nine slot members from `CRealPrelude`'s own
/// theorems and declares nothing.
#[must_use]
pub fn minted_axioms_of(footprint: &[String]) -> Vec<String> {
    footprint
        .iter()
        .filter(|name| name.starts_with("axeyum.reconstruct.") && !is_query_local(name))
        .cloned()
        .collect()
}

/// The entries of a footprint that are assumptions of the **carrier**.
///
/// Everything outside the `axeyum.reconstruct.` namespace. Over the `Real`
/// package that is 8-17 of its 30 axioms; over the constructed reals it is
/// empty, which is the measurement this predicate exists to make falsifiable.
///
/// Pair it with [`minted_axioms_of`]: this one alone cannot see an assumption a
/// route declared under its own namespace.
#[must_use]
pub fn carrier_axioms_of(footprint: &[String]) -> Vec<String> {
    footprint
        .iter()
        .filter(|name| !name.starts_with("axeyum.reconstruct."))
        .cloned()
        .collect()
}

/// Which of the kernel's own equality constants a term still mentions, rendered
/// and deduplicated.
///
/// Scans for `Eq`, `Eq.refl` and `Eq.rec` — the inductive, its constructor and
/// its recursor. A proof built through the equality slot mentions none of them at
/// the carrier; one that skipped a helper mentions at least `Eq.rec`.
#[must_use]
pub fn residual_eq_constants(ctx: &LraReconstructCtx, expr: ExprId) -> Vec<String> {
    let logic = ctx.arith.logic;
    let targets = [logic.eq, logic.eq_refl, logic.eq_rec];
    let mut found: std::collections::BTreeSet<String> = std::collections::BTreeSet::new();
    let mut seen: std::collections::BTreeSet<ExprId> = std::collections::BTreeSet::new();
    let mut stack = vec![expr];
    while let Some(node) = stack.pop() {
        if !seen.insert(node) {
            continue;
        }
        match *ctx.kernel.expr_node(node) {
            ExprNode::Const(name, _) => {
                if targets.contains(&name) {
                    found.insert(ctx.kernel.display_name(name).to_string());
                }
            }
            ExprNode::App(a, b) => {
                stack.push(a);
                stack.push(b);
            }
            ExprNode::Proj(_, _, inner) => stack.push(inner),
            ExprNode::Lam(_, ty, body, _) | ExprNode::Pi(_, ty, body, _) => {
                stack.push(ty);
                stack.push(body);
            }
            ExprNode::Let(_, ty, value, body) => {
                stack.push(ty);
                stack.push(value);
                stack.push(body);
            }
            ExprNode::BVar(_) | ExprNode::FVar(_) | ExprNode::Sort(_) | ExprNode::Lit(_) => {}
        }
    }
    found.into_iter().collect()
}

#[cfg(test)]
mod ordered_ring_tests;
