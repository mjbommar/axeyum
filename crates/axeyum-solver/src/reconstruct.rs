//! Alethe → Lean proof reconstruction over the EUF / equality fragment
//! (Track 3, phase P3.7 — the first slice).
//!
//! This module closes the loop from axeyum's Alethe proofs to a
//! **Lean-kernel-checked** proof term. The bridge established here is the
//! equality fragment: an Alethe `eq_reflexive`/`eq_symmetric`/`eq_transitive`
//! step is translated into a Lean [`ExprId`] proof term whose type the trusted
//! [`Kernel`] `infer`s to the corresponding `Eq` proposition.
//!
//! ## The EUF model
//!
//! Reconstruction runs in a fixed first-order model:
//!
//! - a single carrier sort `α : Type` (i.e. `Sort 1`), declared as an axiom;
//! - each uninterpreted Alethe atom (`a`, `b`, …) is a distinct constant of
//!   type `α`, declared as an axiom of type `α` on first use;
//! - each uninterpreted unary function symbol `f` (as in `(f a)`) is a constant
//!   of type `α → α`, declared as an axiom on first use;
//! - an Alethe equality term `(= s t)` translates to the Lean proposition
//!   `Eq.{1} α ⟦s⟧ ⟦t⟧` (the prelude's `Eq`, applied to the sort then the two
//!   translated operands).
//!
//! The atom/function declarations are deterministic: a stable insertion-ordered
//! map keys atom names → their interned constant [`NameId`], so identical
//! Alethe inputs reconstruct to identical kernel terms.
//!
//! ## Soundness — the kernel is the checker
//!
//! A reconstructed step is accepted **only** when the kernel `infer`s its proof
//! term and that inferred type is [`Kernel::def_eq`] to the expected (translated)
//! conclusion proposition. A wrong motive or a wrong `Eq.rec` term makes the
//! kernel's `infer` fail or yield a different proposition, and reconstruction
//! returns a [`ReconstructError`] — never a false "checked". The trusted small
//! checker validates the reconstruction; this module is untrusted glue.
//!
//! ## Scope of this slice
//!
//! Only the equality rules `eq_reflexive`, `eq_symmetric`, and `eq_transitive`
//! over atoms (with optional simple unary function applications in the term
//! translator) are reconstructed. Resolution, the refutation-to-`False` glue,
//! bit-blasting, congruence (`eq_congruent`), and the arithmetic rules are later
//! slices and are rejected here with a clear error rather than guessed.
// The Eq/Eq.rec terms are inherently dense in single-letter operand names
// (`a`, `b`, `c`, …) and in close de-Bruijn-indexed bindings (`eq_a_x`/`eq_b_x`),
// mirroring the prelude's own proof-term builders; the pedantic name lints fight
// that without improving clarity here.
#![allow(clippy::similar_names, clippy::many_single_char_names)]

mod arithmetic;
mod bitblast;
mod cnf;
mod datatype;
mod direct;
mod equality;
mod quantifier;
mod quant_bv_instance_set_lean;
mod resolution;

pub use arithmetic::{LraReconstructCtx, reconstruct_lra_proof, reconstruct_sos_proof};
pub use bitblast::{
    prove_const_shift_lowering_to_lean_module, reconstruct_bitblast_step,
    reconstruct_const_shift_lowering, reconstruct_qf_bv_proof, reconstruct_qf_ufbv_proof,
};
pub use cnf::reconstruct_cnf_intro_rule;
pub use equality::reconstruct_eq_step;
pub use quantifier::{reconstruct_quant_unsat_proof, reconstruct_skolem_unsat_proof};
pub use quant_bv_instance_set_lean::{
    reconstruct_bv_alternation_counterexample_to_lean_module,
    reconstruct_bv_closed_universal_counterexample_to_lean_module,
    reconstruct_bv_conjunctive_universal_instance_to_lean_module,
    reconstruct_bv_paired_existential_transfer_to_lean_module,
    reconstruct_bv_positive_universal_instance_set_to_lean_module,
    reconstruct_bv_vacuous_exists_universal_counterexample_to_lean_module,
    reconstruct_negated_existential_witness_to_lean_module,
};
pub use resolution::reconstruct_resolution_proof;

use std::collections::{BTreeMap, BTreeSet};

use axeyum_cnf::{AletheCommand, AletheLit, AletheTerm};
use axeyum_ir::{
    FuncId, Op as IrOp, Rational, Sort as IrSort, TermArena, TermId, TermNode as IrTermNode,
};
use axeyum_lean_kernel::{
    BinderInfo, DatatypeFamily, DatatypeInductive, Declaration, ExprId, Kernel, LevelId,
    LocalContext, LocalDecl, LogicPrelude, NameId, RecField, RecursiveDatatypeFamily,
    build_logic_prelude,
};

use datatype::{
    reconstruct_qf_dt_acyclic_to_lean_module, reconstruct_qf_dt_distinct_to_lean_module,
    reconstruct_qf_dt_injective_to_lean_module, reconstruct_qf_dt_tester_to_lean_module,
};
use arithmetic::{
    clear_rational_sos_denominators, is_disjunctive_lra_refutation,
    real_to_lin, reconstruct_disjunctive_lra_proof,
};
use cnf::{
    Assignment, and_chain_prop_of, and_intro, and_intro_fold, and_project, iff_intro,
    prove_clause_by_cases,
};
use bitblast::{
    bit_of_operand_resolves, bv_bit, reconstruct_bitwise_cps_tail, reconstruct_bitwise_step,
};
#[cfg(test)]
use bitblast::{collect_congruence_blocks, euf_refutation_for_test};
#[cfg(test)]
use arithmetic::{try_general_farkas, try_mixed_farkas};
#[cfg(test)]
use datatype::{
    build_nat_discriminator, build_nat_ne_succ, build_nat_ne_succ_m_succ,
    build_nat_ne_succ_m_zero, build_nat_ne_succ_pow, build_nat_ne_succ_pow_m_succ,
    build_nat_ne_succ_pow_m_zero, build_nat_pred,
};
use equality::{reconstruct_eq_congruent, reconstruct_eq_transitive_n, reconstruct_symm};
#[cfg(test)]
use quantifier::declare_forall_axiom;
use resolution::{
    Clause, CpsClause, apply_cps_clause, check_false_prop, clause_to_cps, cps_clause_prop, ex_falso,
    double_negation_elim, fresh_fvar_id, normalize_cps_clause, normalize_lit_polarity, or_inl,
    or_inr, reconstruct_ordered_rup_cps_step, reconstruct_resolution_step,
};

/// An error from Alethe → Lean reconstruction. Every out-of-scope shape, unknown
/// rule, or kernel rejection surfaces here; reconstruction never panics on
/// malformed or out-of-scope input.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ReconstructError {
    /// An Alethe term whose shape this slice does not translate (e.g. an
    /// equality of the wrong arity, an indexed operator, or a function symbol of
    /// unsupported arity).
    UnsupportedTerm {
        /// A human-readable s-expression key for the offending term.
        term: String,
    },
    /// A rule outside this slice's equality fragment (resolution, bit-blasting,
    /// arithmetic, `eq_congruent`, …).
    UnsupportedRule {
        /// The unsupported rule name.
        rule: String,
    },
    /// A step's premise/conclusion shape did not match the rule's expected form
    /// (e.g. an `eq_symmetric` whose conclusion is not `(= b a)` of the premise
    /// `(= a b)`, or a wrong premise count).
    MalformedStep {
        /// The rule whose step was malformed.
        rule: String,
        /// What was wrong, for diagnostics.
        detail: String,
    },
    /// The kernel rejected the reconstructed proof term: either `infer` returned
    /// an error, or the inferred proposition was not definitionally equal to the
    /// expected (translated) conclusion. This is the soundness gate firing.
    KernelRejected {
        /// The rule whose reconstructed term the kernel rejected.
        rule: String,
        /// A diagnostic describing the rejection (infer error or type mismatch).
        detail: String,
    },
    /// A `resolution`/`th_resolution` step whose premise/conclusion shape this
    /// EUF slice does not reconstruct (e.g. a premise id is unknown, a non-Horn
    /// theory clause, or a closing resolution whose premises are not a
    /// complementary equality/disequality unit pair).
    UnsupportedResolution {
        /// What was wrong, for diagnostics.
        detail: String,
    },
    /// A reference to a step/assume id that the proof never defined before its
    /// use (premise ordering or a typo in the emitted proof).
    UnknownPremise {
        /// The undefined premise identifier.
        id: String,
    },
    /// The proof walked to completion without a resolution step deriving the
    /// empty clause `(cl)` — so there is no `False` to return.
    NoEmptyClause,
}

impl core::fmt::Display for ReconstructError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            ReconstructError::UnsupportedTerm { term } => {
                write!(f, "unsupported Alethe term for reconstruction: {term}")
            }
            ReconstructError::UnsupportedRule { rule } => {
                write!(f, "unsupported Alethe rule for reconstruction: `{rule}`")
            }
            ReconstructError::MalformedStep { rule, detail } => {
                write!(f, "malformed `{rule}` step: {detail}")
            }
            ReconstructError::KernelRejected { rule, detail } => {
                write!(f, "kernel rejected reconstructed `{rule}` term: {detail}")
            }
            ReconstructError::UnsupportedResolution { detail } => {
                write!(
                    f,
                    "unsupported resolution shape for reconstruction: {detail}"
                )
            }
            ReconstructError::UnknownPremise { id } => {
                write!(f, "reference to undefined premise `{id}`")
            }
            ReconstructError::NoEmptyClause => {
                write!(f, "proof does not derive the empty clause `(cl)`")
            }
        }
    }
}

impl core::error::Error for ReconstructError {}

struct GatePropAlias {
    fvar: u64,
    name: NameId,
    value: ExprId,
}

#[derive(Default)]
struct ClosedAliasMode {
    gate_props: bool,
    cps_clauses: bool,
}

/// The reconstruction context: a [`Kernel`] seeded with the logical prelude, the
/// EUF carrier sort `α : Type`, and a deterministic map from Alethe atom/function
/// names to their interned constant [`NameId`].
///
/// Atom constants have type `α`; an arity-`n` function constant has type
/// `α → … → α` (`n` arrows). Declarations are added to the kernel's environment
/// lazily, the first time an atom/function name is seen.
pub struct ReconstructCtx {
    kernel: Kernel,
    /// Locals in scope while reconstructing proof steps underneath genuine
    /// quantifier eliminators. Empty for the ordinary closed Alethe routes.
    local_ctx: LocalContext,
    /// Build open proof terms without re-inferring every intermediate Alethe
    /// command. The completed closed term still passes the authoritative kernel
    /// gate; this avoids quadratic checking below large quantifier prefixes.
    defer_open_step_checks: bool,
    prelude: LogicPrelude,
    /// The universe level `1` (so the carrier `α : Sort 1 = Type`).
    one: LevelId,
    /// The carrier sort `α`, a `Const` of an `Axiom : Type`.
    alpha: ExprId,
    /// Deterministic atom/function name → constant `NameId` (insertion order is
    /// id order; a `BTreeMap` keeps lookup/serialization stable).
    atoms: BTreeMap<String, NameId>,
    /// Function symbol name → its `α → α` constant `NameId`.
    funcs: BTreeMap<String, NameId>,
    /// Deterministic propositional-atom name → `Prop` constant `NameId`. These are
    /// the Boolean atoms of the **clausal** layer (a CNF variable / SAT atom), each
    /// an opaque `Axiom : Prop` — distinct from the EUF carrier-sort `atoms` above.
    prop_atoms: BTreeMap<String, NameId>,
    /// The classical excluded-middle axiom `em : Π (p : Prop), Or p (Not p)`,
    /// declared lazily on first use by the resolution layer (`None` until then).
    /// This is the *only* addition to the trusted base for propositional
    /// resolution; it is the honest, faithful encoding because axeyum's solver is
    /// classical. Note: the binary-resolution reconstruction this module builds is
    /// in fact constructive (it case-splits on a premise it already holds), so it
    /// does not consume `em`; `em` is declared to make the classical commitment
    /// explicit and available for the general (pivot-free) shape.
    em: Option<NameId>,
    /// The **bit-blast bridge** for the fused bitwise `QF_BV` walk (slice 6).
    ///
    /// When `Some`, the clausal/gate translation runs in **bit mode**: a key is the
    /// s-expression of a bit-vector predicate atom (e.g. `(= (bvand a b) a)`) and
    /// its value is that predicate's bit-level Boolean form `B` (e.g.
    /// `(= (and ((_ @bit_of 0) a) ((_ @bit_of 0) b)) ((_ @bit_of 0) a))`), learned
    /// from the proof's `equiv1`/`equiv2` bridge clauses. Any atom whose key is in
    /// the map is translated as its `B` form, so a predicate's `Prop` is
    /// *definitionally* its bit-level form. This makes the `bitblast_*`/`cong`/
    /// `trans`/`equiv1`/`equiv2` bridge **reflexive**: the bridge clauses become
    /// genuine `Prop` tautologies (`¬B ∨ B`) rather than opaque axioms, so the
    /// reconstructed `False` is closed over only the input-assumption hypotheses.
    ///
    /// When `None` (the default, EUF/propositional/per-step paths) the clausal
    /// translation is the original opaque one — atoms are uninterpreted Props.
    bridge: Option<BTreeMap<String, AletheTerm>>,
    /// Roles under which hypothesis/`em` axioms were declared during a
    /// reconstruction, keyed by the declared `NameId`. Used to *audit* closedness:
    /// after a fused bitwise walk the only non-prelude axioms must be the input
    /// `assume` hypotheses and `em` — no `bridge`/`cong`/`trans`/`bitblast` axiom.
    axiom_roles: BTreeMap<NameId, String>,
    /// Monotone counter for generating fresh, collision-free declaration names
    /// under a private namespace, so reconstructed atoms never clash with the
    /// prelude's names.
    next_id: u64,
    /// Bit-vector symbol/literal name → width, learned from each `bitblast_var` /
    /// `bitblast_const` step (its `@bbterm` conclusion has exactly width bits).
    /// Bit-blasting is bottom-up, so a structural consumer (`concat`) sees its
    /// operands' widths recorded by the time its own step is reconstructed.
    bv_widths: BTreeMap<String, usize>,
    /// Kernel `BitVec w` models used by quantified-BV source reconstruction.
    bv_value_types: BTreeMap<usize, DatatypeInductive>,
    /// Computational-`Bool` bit-vector models for concrete witness reduction.
    computational_bv_value_types: BTreeMap<usize, DatatypeInductive>,
    /// Shared reducible computational Bool operators used by AIG source terms.
    computational_bool_not: Option<NameId>,
    computational_bool_and: Option<NameId>,
    /// Free bit-vector symbol → `(width, kernel constant)` in the typed bit model.
    bv_value_symbols: BTreeMap<String, (usize, NameId)>,
    /// Scoped Bool binder names and their kernel values while translating a source
    /// quantifier body.
    gate_bound_bools: BTreeMap<String, ExprId>,
    /// Scoped BV binder names and their `(width, kernel value)` while translating a
    /// source quantifier body.
    gate_bound_bvs: BTreeMap<String, (usize, ExprId)>,
    /// Whether bare BV projections use the typed finite-bit model instead of opaque
    /// propositional atoms.
    typed_bv_gates: bool,
    /// Memoization for [`ReconstructCtx::gate_term_to_prop`]: `AletheTerm` key → its
    /// `Prop` `ExprId`. The bit-blast gates (esp. lowered multipliers/dividers) repeat
    /// shared subterms heavily; without this the CNF-intro rules rebuild them every
    /// time. **Cleared on any `bridge` change** (the result depends on the bridge).
    gate_memo: BTreeMap<String, ExprId>,
    /// Scope-preserving aliases for witness-dependent gate propositions. These
    /// open DAG nodes cannot be hoisted as closed module definitions, so compact
    /// quantified reconstruction records them as explicit local `let`s.
    gate_prop_aliases: Option<Vec<GatePropAlias>>,
    /// Closed-route gate propositions may be admitted as transparent checked
    /// definitions, allowing later proof declarations to reference constants
    /// instead of remaining underneath one enormous local-let telescope. In the
    /// same mode, nonempty CPS clauses may become checked theorem declarations.
    closed_aliases: ClosedAliasMode,
    /// First checked-definition admission failure recorded by the infallible
    /// gate translator and surfaced at the enclosing reconstruction boundary.
    global_gate_prop_alias_error: Option<String>,
    /// **Route-A datatype registry.** Maps a datatype constructor key
    /// `"<arity>_<ctorname>"` (parsed from the reserved `!dtcon_n_c` /
    /// `!dtsel_n_i_c` heads the datatype-elim emitter renders) to the kernel
    /// inductive `D` modeling that constructor: `D : α` (the EUF carrier sort)
    /// with one constructor `D.mk : α → … → D` of the recorded arity. Declared
    /// lazily on the first datatype term seen. Modeling the SMT datatype as a
    /// kernel inductive makes the read-over-construct projection `select_i(C a…)`
    /// an **ι-reduction** (`Eq.refl`), so the datatype-elim certificate carries
    /// **no assumed projection axiom** (zero-trust datatypes).
    datatypes: BTreeMap<String, DatatypeInductive>,
    /// **Route-A datatype FAMILY registry** for the is-tester fold. Maps a
    /// datatype's name (the SMT `DatatypeId`'s name) to the kernel
    /// **multi-constructor** inductive `D : α` carrying *every* constructor of
    /// that datatype (`D.c₀ … D.c_{k-1}`), declared lazily the first time a
    /// tester over the datatype is seen. The family lets the is-tester recursor
    /// distinguish constructors, so `is_C (cⱼ x…)` ι-reduces to a concrete
    /// `Bool` value — the is-tester fold is `Eq.refl Bool`, no assumed axiom.
    datatype_families: BTreeMap<String, DatatypeFamily>,
}

impl core::fmt::Debug for ReconstructCtx {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("ReconstructCtx")
            .field("atoms", &self.atoms.keys().collect::<Vec<_>>())
            .field("funcs", &self.funcs.keys().collect::<Vec<_>>())
            .finish_non_exhaustive()
    }
}

impl Default for ReconstructCtx {
    fn default() -> Self {
        Self::new()
    }
}

impl ReconstructCtx {
    /// Build a fresh reconstruction context: a kernel with the logical prelude,
    /// the carrier sort `α : Type` declared, and empty atom/function maps.
    ///
    /// # Panics
    ///
    /// Panics only if the fixed, known-good carrier-sort axiom fails to admit,
    /// which would indicate a kernel regression rather than a caller error.
    #[must_use]
    pub fn new() -> Self {
        let mut kernel = Kernel::new();
        let prelude = build_logic_prelude(&mut kernel);
        let anon = kernel.anon();

        // α : Sort 1 (= Type). Declared as an axiom so it is a genuine `Const`.
        let one = {
            let z = kernel.level_zero();
            kernel.level_succ(z)
        };
        let type_ = kernel.sort(one);
        let alpha_name = kernel.name_str(anon, "α");
        kernel
            .add_declaration(Declaration::Axiom {
                name: alpha_name,
                uparams: vec![],
                ty: type_,
            })
            .expect("carrier sort axiom α : Type should admit");
        let alpha = kernel.const_(alpha_name, vec![]);

        Self {
            kernel,
            local_ctx: LocalContext::new(),
            defer_open_step_checks: false,
            prelude,
            one,
            alpha,
            atoms: BTreeMap::new(),
            funcs: BTreeMap::new(),
            prop_atoms: BTreeMap::new(),
            em: None,
            bridge: None,
            axiom_roles: BTreeMap::new(),
            next_id: 0,
            bv_widths: BTreeMap::new(),
            bv_value_types: BTreeMap::new(),
            computational_bv_value_types: BTreeMap::new(),
            computational_bool_not: None,
            computational_bool_and: None,
            bv_value_symbols: BTreeMap::new(),
            gate_bound_bools: BTreeMap::new(),
            gate_bound_bvs: BTreeMap::new(),
            typed_bv_gates: false,
            gate_memo: BTreeMap::new(),
            gate_prop_aliases: None,
            closed_aliases: ClosedAliasMode::default(),
            global_gate_prop_alias_error: None,
            datatypes: BTreeMap::new(),
            datatype_families: BTreeMap::new(),
        }
    }

    /// A shared reference to the underlying kernel (e.g. to `infer`/`def_eq` an
    /// externally-built term, or to inspect the environment).
    #[must_use]
    pub fn kernel(&self) -> &Kernel {
        &self.kernel
    }

    /// A mutable reference to the underlying kernel.
    pub fn kernel_mut(&mut self) -> &mut Kernel {
        &mut self.kernel
    }

    /// The logical prelude names (`Eq`, `Eq.refl`, `Eq.rec`, …).
    #[must_use]
    pub fn prelude(&self) -> &LogicPrelude {
        &self.prelude
    }

    /// The carrier sort `α` expression.
    #[must_use]
    pub fn alpha(&self) -> ExprId {
        self.alpha
    }

    /// The multiset of **roles** under which hypothesis/`em` axioms have been
    /// declared so far (e.g. `"assume"`, `"em"`, or a bridge rule name). This is the
    /// closedness-audit surface for the fused bitwise walk: after
    /// [`reconstruct_qf_bv_proof`] the only roles present must be `"assume"` (the
    /// input `QF_BV` predicate hypotheses) and `"em"` — never a `"cong"`/`"trans"`/
    /// `"equiv1"`/`"equiv2"`/`"bitblast_*"` bridge axiom.
    ///
    /// The roles are returned sorted for determinism.
    #[must_use]
    pub fn declared_axiom_roles(&self) -> Vec<String> {
        let mut roles: Vec<String> = self.axiom_roles.values().cloned().collect();
        roles.sort();
        roles
    }

    /// Mint a fresh private name component under the anonymous root, used to
    /// keep generated atom/function declarations from colliding with each other
    /// or the prelude. The counter is deterministic.
    fn fresh_name(&mut self, base: &str) -> NameId {
        let anon = self.kernel.anon();
        let ns = self.kernel.name_str(anon, "axeyum.reconstruct");
        let id = self.next_id;
        self.next_id += 1;
        let with_base = self.kernel.name_str(ns, base);
        self.kernel.name_num(with_base, id)
    }

    /// Get (declaring lazily) the constant `NameId` for an uninterpreted atom of
    /// type `α`. Idempotent: the same atom name always maps to the same constant.
    fn atom_const(&mut self, name: &str) -> NameId {
        if let Some(&id) = self.atoms.get(name) {
            return id;
        }
        let decl_name = self.fresh_name("atom");
        self.kernel
            .add_declaration(Declaration::Axiom {
                name: decl_name,
                uparams: vec![],
                ty: self.alpha,
            })
            .expect("atom axiom (_ : α) should admit");
        self.atoms.insert(name.to_owned(), decl_name);
        decl_name
    }

    /// Get (declaring lazily) the constant `NameId` for an uninterpreted
    /// function symbol of arity `arity`, type `α → … → α`. Idempotent (the arity
    /// is fixed per name in well-formed input, so the first declaration wins).
    fn func_const(&mut self, name: &str, arity: usize) -> NameId {
        if let Some(&id) = self.funcs.get(name) {
            return id;
        }
        let anon = self.kernel.anon();
        // α → α → … → α  (`arity` arrows), i.e. Π (_ : α)^arity, α.
        let mut ty = self.alpha;
        for _ in 0..arity {
            ty = self.kernel.pi(anon, self.alpha, ty, BinderInfo::Default);
        }
        let decl_name = self.fresh_name("func");
        self.kernel
            .add_declaration(Declaration::Axiom {
                name: decl_name,
                uparams: vec![],
                ty,
            })
            .expect("function axiom (_ : α → … → α) should admit");
        self.funcs.insert(name.to_owned(), decl_name);
        decl_name
    }

    /// Get (declaring lazily) the **route-A datatype inductive** for the reserved
    /// head `head` (a `!dtcon_n_c` / `!dtsel_n_i_c` name) of constructor arity
    /// `arity`. Idempotent per constructor key `"<arity>_<ctorname>"`, so the
    /// constructor and all its selectors share one kernel inductive `D : α` with a
    /// single constructor `D.mk : α → … → D`.
    ///
    /// Modeling the SMT datatype constructor as a kernel constructor makes the
    /// selector a recursor application, so `select_i(C a…)` ι-reduces to `a_i` —
    /// the read-over-construct projection is **ι-reduction**, not an assumed axiom.
    fn datatype_inductive(
        &mut self,
        head: &str,
        arity: usize,
    ) -> Result<DatatypeInductive, ReconstructError> {
        // Key by arity + ctor name so a constructor and its selectors coincide.
        let key = datatype_key(head).ok_or_else(|| ReconstructError::UnsupportedTerm {
            term: head.to_owned(),
        })?;
        if let Some(&dt) = self.datatypes.get(&key) {
            return Ok(dt);
        }
        let decl_name = self.fresh_name("dt");
        let alpha = self.alpha;
        let one = self.one;
        let dt = self
            .kernel
            .add_datatype_inductive(decl_name, alpha, one, arity)
            .map_err(|e| ReconstructError::KernelRejected {
                rule: "datatype".to_owned(),
                detail: format!("datatype inductive did not admit: {e:?}"),
            })?;
        self.datatypes.insert(key, dt);
        Ok(dt)
    }

    /// Get (declaring lazily) the **route-A datatype FAMILY** for the SMT
    /// datatype named `dt_name`, whose constructors are `(leaf_name, arity)` in
    /// declaration order. The kernel constructors are named **under** the family
    /// inductive (`<family>.<leaf>`), so that when the family is rendered as a real
    /// Lean `inductive` the auto-generated constructor/recursor names match Lean's.
    /// Idempotent per `dt_name`.
    fn datatype_family(
        &mut self,
        dt_name: &str,
        ctors: &[(String, usize)],
    ) -> Result<DatatypeFamily, ReconstructError> {
        if let Some(fam) = self.datatype_families.get(dt_name) {
            return Ok(fam.clone());
        }
        let decl_name = self.fresh_name("dtfam");
        let ctor_decls: Vec<(NameId, usize)> = ctors
            .iter()
            .map(|(leaf, arity)| (self.kernel.name_str(decl_name, leaf.as_str()), *arity))
            .collect();
        let alpha = self.alpha;
        let one = self.one;
        let fam = self
            .kernel
            .add_datatype_family(decl_name, alpha, one, &ctor_decls)
            .map_err(|e| ReconstructError::KernelRejected {
                rule: "datatype_tester".to_owned(),
                detail: format!("datatype family did not admit: {e:?}"),
            })?;
        self.datatype_families
            .insert(dt_name.to_owned(), fam.clone());
        Ok(fam)
    }

    /// Get (declaring) the **route-A RECURSIVE datatype FAMILY** for the SMT
    /// datatype named `dt_name`, whose constructors are `(leaf_name, field-shapes)`
    /// in declaration order — each field shaped [`RecField::Carrier`] (`α`) or
    /// [`RecField::Recursive`] (the datatype `D` itself). The recursive twin of
    /// [`ReconstructCtx::datatype_family`], used by the **acyclicity** route so the
    /// `tail : D` field is the inductive's own sort and the size measure recurses.
    /// Not memoized (acyclicity declares one family per refutation module), so it
    /// takes the constructor shapes directly rather than a datatype-name key.
    fn recursive_datatype_family(
        &mut self,
        ctors: &[(String, Vec<RecField>)],
    ) -> Result<RecursiveDatatypeFamily, ReconstructError> {
        let decl_name = self.fresh_name("dtrec");
        let ctor_decls: Vec<(NameId, Vec<RecField>)> = ctors
            .iter()
            .map(|(leaf, shapes)| {
                (
                    self.kernel.name_str(decl_name, leaf.as_str()),
                    shapes.clone(),
                )
            })
            .collect();
        let alpha = self.alpha;
        let one = self.one;
        self.kernel
            .add_recursive_datatype_family(decl_name, alpha, one, &ctor_decls)
            .map_err(|e| ReconstructError::KernelRejected {
                rule: "datatype_acyclic".to_owned(),
                detail: format!("recursive datatype family did not admit: {e:?}"),
            })
    }

    /// Build the Lean proposition `Eq.{1} Bool l r` over the computational `Bool`.
    fn mk_eq_bool(&mut self, l: ExprId, r: ExprId) -> ExprId {
        let bool_const = self.kernel.const_(self.prelude.bool_, vec![]);
        let eq = self.kernel.const_(self.prelude.eq, vec![self.one]);
        let e = self.kernel.app(eq, bool_const);
        let e = self.kernel.app(e, l);
        self.kernel.app(e, r)
    }

    /// Build `Eq.refl.{1} Bool a` (the is-tester fold proof, when `a` is the
    /// ι-reduced `Bool` value `is_C (cⱼ x…)` `def_eq`).
    fn mk_eq_refl_bool(&mut self, a: ExprId) -> ExprId {
        let bool_const = self.kernel.const_(self.prelude.bool_, vec![]);
        let refl = self.kernel.const_(self.prelude.eq_refl, vec![self.one]);
        let e = self.kernel.app(refl, bool_const);
        self.kernel.app(e, a)
    }

    /// `f` applied to `args` (left-nested application `f a0 a1 … a_{n-1}`).
    fn apply_func(&mut self, f_name: NameId, args: &[ExprId]) -> ExprId {
        let mut e = self.kernel.const_(f_name, vec![]);
        for &a in args {
            e = self.kernel.app(e, a);
        }
        e
    }

    /// `f` applied to `args` with position `hole` replaced by `hole_expr` (used to
    /// build the per-argument congruence motive's right-hand application).
    fn apply_func_with_hole(
        &mut self,
        f_name: NameId,
        args: &[ExprId],
        hole: usize,
        hole_expr: ExprId,
    ) -> ExprId {
        let mut e = self.kernel.const_(f_name, vec![]);
        for (j, &a) in args.iter().enumerate() {
            let arg = if j == hole { hole_expr } else { a };
            e = self.kernel.app(e, arg);
        }
        e
    }

    /// Build the Lean proposition `Eq.{1} α l r`.
    fn mk_eq(&mut self, l: ExprId, r: ExprId) -> ExprId {
        let eq = self.kernel.const_(self.prelude.eq, vec![self.one]);
        let e = self.kernel.app(eq, self.alpha);
        let e = self.kernel.app(e, l);
        self.kernel.app(e, r)
    }

    /// Build `Eq.refl.{1} α a`.
    fn mk_eq_refl(&mut self, a: ExprId) -> ExprId {
        let refl = self.kernel.const_(self.prelude.eq_refl, vec![self.one]);
        let e = self.kernel.app(refl, self.alpha);
        self.kernel.app(e, a)
    }

    /// Translate an Alethe term into a Lean [`ExprId`] in the EUF model.
    ///
    /// - an atom `Const(s)` → the constant of the axiom `s : α`;
    /// - an equality `App("=", [s, t])` → `Eq.{1} α ⟦s⟧ ⟦t⟧`;
    /// - an n-ary function application `App(f, [x1,…,xn])` → `f ⟦x1⟧ … ⟦xn⟧`
    ///   where `f : α → … → α`.
    ///
    /// # Errors
    ///
    /// Returns [`ReconstructError::UnsupportedTerm`] for any other shape: an
    /// equality of non-2 arity, an indexed operator, or a function symbol of
    /// arity other than 1 (the boundary of this slice).
    pub fn alethe_term_to_expr(&mut self, term: &AletheTerm) -> Result<ExprId, ReconstructError> {
        match term {
            AletheTerm::Const(symbol) => {
                let name = self.atom_const(symbol);
                Ok(self.kernel.const_(name, vec![]))
            }
            AletheTerm::App(head, args) if head == "=" => {
                let [l, r] = args.as_slice() else {
                    return Err(ReconstructError::UnsupportedTerm { term: term.key() });
                };
                let l = self.alethe_term_to_expr(l)?;
                let r = self.alethe_term_to_expr(r)?;
                Ok(self.mk_eq(l, r))
            }
            // Route-A datatype constructor `(!dtcon_n_c x0 … x_{n-1})`: the kernel
            // inductive's constructor applied to the field translations.
            AletheTerm::App(head, args) if parse_dtcon(head).is_some() => {
                let (arity, _key) = parse_dtcon(head)
                    .filter(|(arity, _)| *arity == args.len())
                    .ok_or_else(|| ReconstructError::UnsupportedTerm { term: term.key() })?;
                let dt = self.datatype_inductive(head, arity)?;
                let mut e = self.kernel.const_(dt.ctor, vec![]);
                for arg in args {
                    let a = self.alethe_term_to_expr(arg)?;
                    e = self.kernel.app(e, a);
                }
                Ok(e)
            }
            // Route-A datatype selector `(!dtsel_n_i_c operand)`: the recursor-based
            // field selector applied to the operand translation. When the operand
            // is a matching constructor application this `def_eq`-reduces (ι) to the
            // selected field — the read-over-construct projection as a theorem.
            AletheTerm::App(head, args) if parse_dtsel(head).is_some() => {
                let (arity, index, _key) = parse_dtsel(head)
                    .filter(|_| args.len() == 1)
                    .ok_or_else(|| ReconstructError::UnsupportedTerm { term: term.key() })?;
                let operand = self.alethe_term_to_expr(&args[0])?;
                let dt = self.datatype_inductive(head, arity)?;
                let alpha = self.alpha;
                let one = self.one;
                let sel = self.kernel.datatype_selector(dt, alpha, one, index);
                Ok(self.kernel.app(sel, operand))
            }
            // An n-ary uninterpreted function application `(f x1 … xn)`, n ≥ 1.
            // (The `=` arm above already consumed equalities, so `head != "="`.)
            AletheTerm::App(head, args) if !args.is_empty() => {
                let f_name = self.func_const(head, args.len());
                let mut e = self.kernel.const_(f_name, vec![]);
                for arg in args {
                    let a = self.alethe_term_to_expr(arg)?;
                    e = self.kernel.app(e, a);
                }
                Ok(e)
            }
            // Indexed operators and any other shape are out of this slice's scope.
            AletheTerm::App(..) | AletheTerm::Indexed { .. } => {
                Err(ReconstructError::UnsupportedTerm { term: term.key() })
            }
        }
    }

    /// Build the `Eq.rec` transport term that, given `h : Eq α p q` and a
    /// `refl_case` proving `motive p (Eq.refl α p)`, yields a proof of
    /// `motive q h`. This is the workhorse for both symmetry and transitivity.
    ///
    /// The motive is supplied as a closed Lean lambda
    /// `motive : fun (x : α) (_ : Eq α p x) => …` (an `Expr`, not opened), and
    /// `p` is the fixed left operand of `h`. The built term is
    /// `Eq.rec.{0,1} α p motive refl_case q h`.
    fn mk_eq_rec_transport(
        &mut self,
        p: ExprId,
        motive: ExprId,
        refl_case: ExprId,
        q: ExprId,
        h: ExprId,
    ) -> ExprId {
        let z = self.kernel.level_zero();
        // Eq.rec.{v=0, u=1}: the motive eliminates into Prop (Eq is a Prop), the
        // carrier lives in Sort 1.
        let rec = self.kernel.const_(self.prelude.eq_rec, vec![z, self.one]);
        let e = self.kernel.app(rec, self.alpha);
        let e = self.kernel.app(e, p); // the fixed param `a`
        let e = self.kernel.app(e, motive);
        let e = self.kernel.app(e, refl_case);
        let e = self.kernel.app(e, q); // the index argument `b`
        self.kernel.app(e, h) // the major `h : Eq α p q`
    }
}

/// Extract the two operands of a positive `(= a b)` literal (the atom is the
/// 2-arity `=` application, not negated).
fn as_positive_eq(lit: &AletheLit) -> Option<(&AletheTerm, &AletheTerm)> {
    if lit.negated {
        return None;
    }
    match &lit.atom {
        AletheTerm::App(head, args) if head == "=" && args.len() == 2 => Some((&args[0], &args[1])),
        _ => None,
    }
}

/// Extract the two operands of a negated `(not (= a b))` literal (here: a
/// `negated` literal whose atom is the 2-arity `=` application).
fn as_negated_eq(lit: &AletheLit) -> Option<(&AletheTerm, &AletheTerm)> {
    if !lit.negated {
        return None;
    }
    match &lit.atom {
        AletheTerm::App(head, args) if head == "=" && args.len() == 2 => Some((&args[0], &args[1])),
        _ => None,
    }
}

/// The soundness gate: `infer` the reconstructed `proof` and require its inferred
/// type to be [`Kernel::def_eq`] to `expected`. On any kernel rejection (infer
/// error or type mismatch) this returns [`ReconstructError::KernelRejected`];
/// otherwise it returns the validated proof term.
fn check_against(
    ctx: &mut ReconstructCtx,
    rule: &str,
    proof: ExprId,
    expected: ExprId,
) -> Result<ExprId, ReconstructError> {
    if ctx.defer_open_step_checks {
        return Ok(proof);
    }
    let inferred = ctx
        .kernel
        .infer_in(proof, &mut ctx.local_ctx)
        .map_err(|e| ReconstructError::KernelRejected {
            rule: rule.to_owned(),
            detail: format!("infer failed: {e:?}"),
        })?;
    if ctx
        .kernel
        .def_eq_in(inferred, expected, &mut ctx.local_ctx)
    {
        Ok(proof)
    } else {
        Err(ReconstructError::KernelRejected {
            rule: rule.to_owned(),
            detail: "inferred proposition is not def-eq to the conclusion".to_owned(),
        })
    }
}

/// What a step/assume id reconstructs to in the clausal EUF walk.
///
/// Every command the EUF emitter produces is either a **unit** equality /
/// disequality clause (carrying a kernel proof of its single literal), or a Horn
/// **theory clause** (`eq_*`/`eq_congruent`: some leading `(not (= …))`
/// hypotheses and one positive `(= …)` conclusion) reconstructed lazily when a
/// `resolution` step resolves it against unit proofs of its hypotheses.
#[derive(Clone)]
enum ClauseProof {
    /// A unit positive equality `(cl (= l r))` with proof `p : Eq α l r`.
    EqUnit {
        l: AletheTerm,
        r: AletheTerm,
        proof: ExprId,
    },
    /// A unit disequality `(cl (not (= l r)))` with proof `p : Not (Eq α l r)`.
    DiseqUnit {
        l: AletheTerm,
        r: AletheTerm,
        proof: ExprId,
    },
    /// A Horn theory clause (`rule` is `eq_transitive`/`eq_symmetric`/
    /// `eq_reflexive`/`eq_congruent`): the full clause, reconstructed into the
    /// proof of its positive literal only when resolved against unit hypotheses.
    TheoryClause {
        rule: String,
        clause: Vec<AletheLit>,
    },
}

/// The proof fragment a goal falls into, for [`prove_unsat_to_lean`] routing.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ProofFragment {
    /// Bit-vectors and/or Booleans (the `QF_BV` core).
    QfBv,
    /// A direct syntactic contradiction `¬(t = t)`.
    ReflexiveDisequality,
    /// A direct negation of a checked term identity such as `ite true t e = t`.
    TermIdentity,
    /// A direct assertion that checked Boolean simplification reduces to `false`.
    BoolSimplification,
    /// Uninterpreted functions over a single sort (no bit-vectors).
    QfUf,
    /// Uninterpreted functions combined with bit-vectors.
    QfUfBv,
    /// A finite-domain pigeonhole refutation over a one-bit UF argument domain.
    FiniteDomainPigeonhole,
    /// An exhaustive refutation over tiny Boolean-UF interpretations.
    BoolUfExhaustive,
    /// An exhaustive Boolean-skeleton refutation whose every skeleton model is
    /// rejected by EUF congruence closure.
    BoolEufExhaustive,
    /// A Boolean-structured EUF refutation checked by the online EUF DPLL(T)
    /// loop.
    BoolEufOnline,
    /// A mixed UF+linear-arithmetic refutation: congruence derives arithmetic
    /// equalities, then arithmetic DPLL refutes the retained residual.
    UfArithCongruence,
    /// A datatype structural refutation by
    /// acyclicity/distinctness/injectivity/exhaustiveness, optionally split over
    /// every branch of a top-level disjunction.
    DatatypeStructural,
    /// An exhaustive finite-domain Bool/BV refutation, including finite
    /// quantifiers, certified by the executable evaluator.
    FiniteDomainEnum,
    /// An exhaustive ground Bool/BV refutation certified by the executable
    /// evaluator.
    TermLevelEnum,
    /// A ground Bool/BV refutation by exhaustive enumeration after checked
    /// top-level definitions and finite-domain restrictions.
    BvDefinedEnum,
    /// A lowered finite-set cardinality contradiction over BV popcounts and
    /// subset/union monotonicity.
    SetCardinality,
    /// A universal BV equality whose left side is a checked non-constant
    /// expression of the quantified variable.
    BvForallNonconstant,
    /// Local finite-BV equality facts plus UF congruence refute the query.
    BvUfLocal,
    /// A direct negation of a checked array axiom schema.
    ArrayAxiom,
    /// A finite-write constant-array default mismatch over an infinite Int index.
    ConstArrayDefaultMismatch,
    /// A finite store-chain readback contradiction over `(Array Int Int)`.
    StoreChainReadback,
    /// A same-index reciprocal-store equality forces an asserted-disequal pair
    /// of arrays equal.
    CrossStoreArrayDisequality,
    /// A Bool-index array has equal concrete reads but disequal arbitrary reads.
    BoolArrayReadCollapse,
    /// A finite BV-index array extensionality refutation.
    FiniteArrayExtensionality,
    /// A certified-unsat scalar BV abstraction of an array query.
    BvAbstraction,
    /// A guarded two-byte memcpy refutation.
    TwoByteMemcpy,
    /// A guarded two-element bubble-sort membership refutation.
    TwoElementBubbleSort,
    /// A guarded two-element selection-sort membership refutation.
    TwoElementSelectionSort,
    /// A two-cell ordinary-swap versus XOR-swap permutation refutation.
    TwoCellXorSwap,
    /// A guarded two-byte XOR-swap round-trip refutation.
    TwoByteXorSwapRoundtrip,
    /// A generated 16-element binary-search miss refutation.
    BinarySearch16,
    /// A generated five-cycle bounded FIFO equivalence refutation.
    FifoBc04,
    /// A guarded aligned byte write-chain commutation refutation.
    AlignedWriteChainCommutation,
    /// Arrays (read-over-write + Ackermann over `select`).
    QfAbv,
    /// Algebraic datatypes (read-over-construct).
    Datatype,
    /// Linear real/integer arithmetic (Farkas).
    Lra,
    /// **Boolean-structured (disjunctive) `QF_LRA`**: a conjunctive linear-real
    /// system plus exactly one clause `(L₁ ∨ L₂)` of non-strict linear-real
    /// literals, where each leaf `conj ∧ Lᵢ` is conjunctive-`Farkas`-refutable.
    /// Reconstructed by a kernel case-split (`Or.rec`/`Or.elim`) on the clause:
    /// each branch reuses the conjunctive general-`Farkas` fold to derive `False`,
    /// and the eliminator combines the two `False` branches into `False`.
    DisjunctiveLra,
    /// Boolean-structured `QF_LRA` certified by the lazy-SMT DPLL(T)
    /// refutation checker: the Boolean skeleton plus learned Farkas-valid
    /// theory lemmas is propositionally unsatisfiable.
    LraDpll,
    /// Boolean-structured linear arithmetic certified by the arithmetic
    /// lazy-SMT DPLL(T) refutation checker over exact integer/real theory
    /// lemmas.
    ArithDpll,
    /// Bounded nonlinear/integer arithmetic certified by the proven-box
    /// bounded-int-blast certificate: a finite integer box, exact covering width,
    /// regenerated DIMACS, and DRAT refutation.
    BoundedIntBlast,
    /// Integer-infeasibility (**Diophantine**) `QF_LIA`: an integer-equality system
    /// that is rational-feasible yet integer-infeasible (`gcd ∤ const`), refuted by
    /// the [`DiophantineCertificate`](crate::DiophantineCertificate) and
    /// reconstructed over the integer prelude (ADR-0042).
    Diophantine,
    /// Integer-**inequality** infeasibility (integer cut) `QF_LIA`: a single-variable
    /// interval `c ≤ k·x ≤ d` (k > 0) whose LP relaxation is feasible yet contains no
    /// integer (no multiple of `k` in `[c, d]`), refuted via discreteness
    /// (`no_int_between`) over the integer prelude (ADR-0042).
    IntInequality,
    /// A trivial single-square sum-of-squares refutation: the one-variable real
    /// query `x*x < 0` (UNSAT: a square is never negative). The simplest SOS
    /// reconstruction, needing no ring normalizer (ADR-0040, SOS slice 1).
    Sos,
    /// A syntactic even-power NRA refutation: a sum of even powers plus a
    /// nonnegative rational constant is asserted strictly negative.
    NraEvenPower,
    /// A top-level universal quantifier.
    Forall,
    /// A closed universal integer equality/disequality refuted by one evaluator-
    /// checked concrete binder assignment and reconstructed by genuine `forall`
    /// elimination over the integer/Bool preludes (ADR-0102).
    ClosedUniversalCounterexample,
    /// A closed universal Bool/BV theorem refuted by a concrete typed binder
    /// assignment and an explicit evaluated AIG proof (ADR-0139).
    BvClosedUniversalCounterexample,
    /// A closed universal Bool/BV theorem below syntactically vacuous leading
    /// existentials, refuted through `Exists.rec` and a typed counterexample.
    BvVacuousExistsUniversalCounterexample,
    /// A closed Bool/BV `forall+ exists+` theorem refuted by a checked outer
    /// counterexample and genuine elimination of the existential suffix.
    BvAlternationCounterexample,
    /// A positive existential witness is transferred through checked `QF_BV`
    /// implications and introduced into a contradicted paired existential.
    BvPairedExistentialTransfer,
    /// The checked ADR-0099 nested-XOR integer theorem reconstructed through
    /// three genuine universal instantiations and propositional case analysis.
    IntNestedXor,
    /// The checked ADR-0095 Euclidean-residue universal reconstructed by
    /// eliminating quotient/remainder witnesses from ADR-0104's general integer
    /// decomposition theorem.
    IntEuclideanResidue,
    /// The checked ADR-0097 positive-slope affine-growth universal reconstructed
    /// through Euclidean decomposition and two guarded consecutive instances.
    IntAffineGrowth,
    /// An ADR-0101 closed Bool/Int equality partition with at most one literal
    /// pivot per Int binder, reconstructed over genuine quantifiers (ADR-0106).
    SinglePivotEqualityPartition,
    /// A finite source-instantiated counterexample cover over free Boolean
    /// guards, reconstructed by bounded excluded-middle case analysis (ADR-0108).
    QuantifiedCounterexampleCover,
    /// A query-scoped set of concrete positive-universal Bool/BV instances whose
    /// residual bit-level refutation is reconstructed from genuine source
    /// instantiations (ADR-0135).
    BvPositiveUniversalInstanceSet,
    /// One concrete instance of a universal reached through a conjunctive
    /// source context, with the residual bit-level refutation reconstructed from
    /// the untouched assertion (ADR-0127).
    BvConjunctiveUniversalInstance,
    /// A concrete evaluator-replayed witness closes a directly negated typed
    /// Bool/BV existential through genuine `Exists.intro` (ADR-0138).
    NegatedExistentialWitness,
    /// A top-level existential quantifier (skolemized).
    Exists,
    /// A word-level (string/sequence) refutation: a contradicted disequality or a
    /// concrete constant clash over the free monoid `Str = List Char`, checked by
    /// the independent word refuter and reconstructed over the string prelude
    /// (P3.7 strings fragment). Cancellation, self-loop/length, and regex-derivative
    /// shapes are deferred (the reconstructor declines them).
    WordEquation,
    /// Empty / no reconstructable content.
    Unsupported,
}

/// Detect the **trivial single-square** SOS shape: `assertions` is exactly one
/// assertion of the form `(x * x) < 0` where `x` is a real-sorted free variable
/// and the right-hand side is the real constant `0`. On a match, returns the
/// [`TermId`] of the real variable `x`; otherwise `None`.
///
/// This is the only shape the slice-1 SOS reconstructor accepts. General SOS
/// (`(x − y)² < 0`, multi-variable squares, etc.) needs the degree-2 ring
/// normalizer and is a later slice — it is deliberately *not* matched here.
#[must_use]
fn is_single_square_lt_zero(arena: &TermArena, assertions: &[TermId]) -> Option<TermId> {
    let [only] = assertions else {
        return None;
    };
    // The assertion must be a real strict-less-than `lhs < rhs`.
    let IrTermNode::App {
        op: IrOp::RealLt,
        args,
    } = arena.node(*only)
    else {
        return None;
    };
    let [lhs, rhs] = &**args else {
        return None;
    };
    let (lhs, rhs) = (*lhs, *rhs);
    // RHS must be the real constant 0.
    match arena.node(rhs) {
        IrTermNode::RealConst(c) if c.is_zero() => {}
        _ => return None,
    }
    // LHS must be `mul x x` with both factors the *same* real variable symbol.
    let IrTermNode::App {
        op: IrOp::RealMul,
        args,
    } = arena.node(lhs)
    else {
        return None;
    };
    let [a, b] = &**args else {
        return None;
    };
    let (a, b) = (*a, *b);
    // Both factors must be the SAME real subterm `ℓ` (interned ⇒ identical `TermId`),
    // and `ℓ` must collect to a LINEAR form expressible in `lin_to_r`'s slice (±1
    // coefficients, a 0/1 constant). Then `ℓ·ℓ` is a single square and the
    // reconstruction succeeds via `sq_nonneg ℓ` with no ring normalizer. A bare real
    // variable `x` is the special case `ℓ = x`. Anything else (coefficient outside
    // ±1, a nonlinear factor, a sum form) declines here and falls through to `Lra`.
    if a != b || arena.sort_of(a) != IrSort::Real {
        return None;
    }
    let lin = real_to_lin(arena, a)?;
    let one = Rational::integer(1);
    let neg_one = Rational::integer(-1);
    if lin.coeffs.iter().any(|&(_, c)| c != one && c != neg_one) {
        return None;
    }
    if !lin.constant.is_zero() && lin.constant != one {
        return None;
    }
    Some(a)
}

/// Match `term` as `mul s t` of two **real variable symbols**, returning their
/// `SymbolId`s `(s, t)` in left-to-right order.
fn match_two_var_mul(
    arena: &TermArena,
    term: TermId,
) -> Option<(axeyum_ir::SymbolId, axeyum_ir::SymbolId)> {
    let IrTermNode::App {
        op: IrOp::RealMul,
        args,
    } = arena.node(term)
    else {
        return None;
    };
    let [a, b] = &**args else {
        return None;
    };
    let (sa, sb) = match (arena.node(*a), arena.node(*b)) {
        (IrTermNode::Symbol(sa), IrTermNode::Symbol(sb)) => (*sa, *sb),
        _ => return None,
    };
    if arena.sort_of(*a) != IrSort::Real || arena.sort_of(*b) != IrSort::Real {
        return None;
    }
    Some((sa, sb))
}

/// Detect the **degree-2 two-variable AM-GM sum form** `x² + y² − 2xy < 0`, the
/// first SOS shape whose asserted lhs is a *sum of monomials* (not a literal
/// `ℓ·ℓ`) — so it needs the degree-2 ring normalizer to prove
/// `Eq R (x²+y²−2xy) ((x−y)·(x−y))` before square-nonnegativity applies.
///
/// The matched IR shape is exactly
/// `RealLt(RealSub(RealAdd(mul x x, mul y y), RealAdd(mul x y, mul x y)), 0)`
/// with `x`, `y` two **distinct** real variable symbols (the cross-term factors
/// may appear in either order, `x·y` or `y·x`). Returns the variable symbols
/// `(x, y)`. Anything else (other monomial sets, three variables, non-unit
/// coefficients, a missing/extra term) returns `None` and falls through — this
/// slice covers only this single shape.
fn is_am_gm_two_var(
    arena: &TermArena,
    assertions: &[TermId],
) -> Option<(axeyum_ir::SymbolId, axeyum_ir::SymbolId)> {
    let [only] = assertions else {
        return None;
    };
    // `lhs < 0`.
    let IrTermNode::App {
        op: IrOp::RealLt,
        args,
    } = arena.node(*only)
    else {
        return None;
    };
    let [lhs, rhs] = &**args else {
        return None;
    };
    match arena.node(*rhs) {
        IrTermNode::RealConst(c) if c.is_zero() => {}
        _ => return None,
    }
    // lhs = RealSub(A, B).
    let IrTermNode::App {
        op: IrOp::RealSub,
        args,
    } = arena.node(*lhs)
    else {
        return None;
    };
    let [a_part, b_part] = &**args else {
        return None;
    };
    // A = RealAdd(mul x x, mul y y).
    let IrTermNode::App {
        op: IrOp::RealAdd,
        args: a_args,
    } = arena.node(*a_part)
    else {
        return None;
    };
    let [a0, a1] = &**a_args else {
        return None;
    };
    let (sx0, sx1) = match_two_var_mul(arena, *a0)?;
    let (sy0, sy1) = match_two_var_mul(arena, *a1)?;
    // First square is `x·x`, second is `y·y`, with `x ≠ y`.
    if sx0 != sx1 || sy0 != sy1 || sx0 == sy0 {
        return None;
    }
    let (sx, sy) = (sx0, sy0);
    // B = RealAdd(xy, xy), each `xy` a product of `x` and `y` (either factor order).
    let IrTermNode::App {
        op: IrOp::RealAdd,
        args: b_args,
    } = arena.node(*b_part)
    else {
        return None;
    };
    let [b0, b1] = &**b_args else {
        return None;
    };
    let is_xy = |t: TermId| -> bool {
        match match_two_var_mul(arena, t) {
            Some((p, q)) => (p == sx && q == sy) || (p == sy && q == sx),
            None => false,
        }
    };
    if !is_xy(*b0) || !is_xy(*b1) {
        return None;
    }
    Some((sx, sy))
}

/// Does `assertions` have an SOS certificate that is a **single perfect square of a
/// ±1-coefficient linear form** (`d = 1`, zero affine row)? This is the general SOS
/// shape [`reconstruct_sos_single_unit_square`] handles via the degree-2 ring
/// normalizer; the classifier uses it to route such queries to [`ProofFragment::Sos`]
/// instead of the linear Farkas path. Cheap-enough: it reuses the same self-checked
/// certificate the reconstructor consumes.
fn is_sos_single_unit_square(arena: &TermArena, assertions: &[TermId]) -> bool {
    match crate::nra_real_root::sos_refute_with_certificate(arena, assertions) {
        Some(cert) => cert.strict_lt() && cert.single_unit_square().is_some(),
        None => false,
    }
}

/// Does `assertions` have an SOS certificate that is a **sum of several perfect
/// squares of ±1-coefficient linear forms** (every `D[k] = 1`, zero affine row)?
/// This is the multi-square shape [`reconstruct_sos_multi_unit_square`] handles; the
/// classifier uses it to route such queries (e.g. `x²+y² < 0`) to
/// [`ProofFragment::Sos`]. The single-square case is its `m = 1` specialization, so
/// `unit_squares` also accepts it — the two classifiers therefore overlap, which is
/// fine (both route to `Sos`).
fn is_sos_multi_unit_square(arena: &TermArena, assertions: &[TermId]) -> bool {
    match crate::nra_real_root::sos_refute_with_certificate(arena, assertions) {
        Some(cert) => cert.strict_lt() && cert.unit_squares().is_some(),
        None => false,
    }
}

/// Does `assertions` have an SOS certificate that is a **RATIONAL-weight sum of
/// squares** `p = Σ dₖ·ℓₖ²` (rational weights, rational/integer linear forms, zero
/// affine row) whose denominators clear within this slice's bounds? This is the
/// shape [`reconstruct_sos_rational_weight`] handles (e.g. 3-variable AM-GM); the
/// classifier uses it to route such queries to [`ProofFragment::Sos`]. Strictly
/// generalizes the ±1/integer-weight classifiers (which also route to `Sos`), so the
/// overlap is fine.
fn is_sos_rational_weight(arena: &TermArena, assertions: &[TermId]) -> bool {
    match crate::nra_real_root::sos_refute_with_certificate(arena, assertions) {
        Some(cert) => {
            cert.strict_lt()
                && cert
                    .rational_squares()
                    .as_deref()
                    .and_then(clear_rational_sos_denominators)
                    .is_some()
        }
        None => false,
    }
}

/// Does `assertions` have an SOS certificate refuting a STRICT `p > 0` atom
/// (`strict_lt == false`) whose squares decompose `−p` and whose denominators clear
/// within this slice's bounds? This is the `p > 0` dual shape
/// [`reconstruct_sos_rational_weight_gt`] handles (e.g. `−x² > 0`, `−x²−y² > 0`);
/// the classifier uses it to route such queries to [`ProofFragment::Sos`] (the
/// strict-inequality classifiers above all require `strict_lt`, so they never match
/// a `p > 0` certificate).
fn is_sos_rational_weight_gt(arena: &TermArena, assertions: &[TermId]) -> bool {
    match crate::nra_real_root::sos_refute_with_certificate(arena, assertions) {
        Some(cert) => {
            !cert.strict_lt()
                && cert
                    .rational_squares()
                    .as_deref()
                    .and_then(clear_rational_sos_denominators)
                    .is_some()
        }
        None => false,
    }
}

fn sos_certificate_certifies(arena: &TermArena, assertions: &[TermId]) -> bool {
    crate::nra_real_root::sos_refute_with_certificate(arena, assertions)
        .is_some_and(|cert| cert.verify())
}

/// Detect a top-level assertion `not (= t t)`. This is a proof-route shortcut,
/// not a simplifier: the original query itself supplies the contradictory
/// disequality, and Lean closes it with `Eq.refl`.
fn reflexive_disequality_assertion(arena: &TermArena, assertions: &[TermId]) -> Option<TermId> {
    for &assertion in assertions {
        let IrTermNode::App {
            op: IrOp::BoolNot,
            args,
        } = arena.node(assertion)
        else {
            continue;
        };
        let [inner] = &**args else {
            continue;
        };
        let IrTermNode::App { op: IrOp::Eq, args } = arena.node(*inner) else {
            continue;
        };
        let [lhs, rhs] = &**args else {
            continue;
        };
        if lhs == rhs {
            return Some(*lhs);
        }
    }
    None
}

const FINITE_DOMAIN_ENUM_CERT_BITS: u32 = 20;

fn term_level_enum_certifies(arena: &TermArena, assertions: &[TermId]) -> bool {
    matches!(
        crate::certify_qf_bv_by_enumeration(arena, assertions, FINITE_DOMAIN_ENUM_CERT_BITS),
        Ok(crate::CertifyOutcome::CertifiedUnsat { .. })
    )
}

fn finite_domain_enum_certifies(arena: &TermArena, assertions: &[TermId]) -> bool {
    matches!(
        crate::certify_finite_bv_by_enumeration(arena, assertions, FINITE_DOMAIN_ENUM_CERT_BITS),
        Ok(crate::CertifyOutcome::CertifiedUnsat { .. })
    )
}

fn scan_ground_bv_proof_fragment(arena: &TermArena, assertions: &[TermId]) -> ProofFragment {
    if assertions.is_empty() {
        ProofFragment::Unsupported
    } else if crate::set_cardinality::set_cardinality_refutation(arena, assertions).is_some() {
        ProofFragment::SetCardinality
    } else if crate::bv_defined_enum::bv_defined_enum_refutation(arena, assertions).is_some() {
        ProofFragment::BvDefinedEnum
    } else if term_level_enum_certifies(arena, assertions) {
        ProofFragment::TermLevelEnum
    } else {
        ProofFragment::QfBv
    }
}

/// Classify `assertions` into the [`ProofFragment`] whose emitter+reconstructor
/// pair handles it, by scanning the operators and sorts that appear. Precedence:
/// a checked finite-domain refutation can own finite Bool/BV quantifier cases,
/// then a generic top-level quantifier wraps any ground theory (`∃` skolemized
/// before `∀`), then the reduction theories (datatype/array), then the
/// mixed/ground cores.
#[must_use]
#[allow(clippy::too_many_lines)]
pub fn scan_proof_fragment(arena: &TermArena, assertions: &[TermId]) -> ProofFragment {
    let mut has_bv = false;
    let mut has_func = false;
    let mut has_uninterpreted_sort = false;
    let mut has_array = false;
    let mut has_datatype = false;
    let mut has_arith = false;
    let mut has_forall = false;
    let mut has_exists = false;
    let mut seen = std::collections::BTreeSet::new();
    let mut stack = assertions.to_vec();
    while let Some(term) = stack.pop() {
        if !seen.insert(term) {
            continue;
        }
        match arena.sort_of(term) {
            IrSort::BitVec(_) => has_bv = true,
            IrSort::Uninterpreted(_) => has_uninterpreted_sort = true,
            IrSort::Array { .. } => has_array = true,
            IrSort::Datatype(_) => has_datatype = true,
            IrSort::Int | IrSort::Real => has_arith = true,
            _ => {}
        }
        if let IrTermNode::App { op, args } = arena.node(term) {
            match op {
                IrOp::Apply(_) => has_func = true,
                IrOp::Select | IrOp::Store => has_array = true,
                IrOp::DtSelect { .. } => has_datatype = true,
                IrOp::Forall(_) => has_forall = true,
                IrOp::Exists(_) => has_exists = true,
                _ => {}
            }
            stack.extend(args.iter().copied());
        }
    }
    if has_exists
        && quant_bv_instance_set_lean::bv_paired_existential_transfer_lean_shape(arena, assertions)
    {
        ProofFragment::BvPairedExistentialTransfer
    } else if crate::word_reconstruct::is_word_equation_shape(arena, assertions) {
        // A pure word (string/sequence) equality/disequality system. The real
        // `unsat` gate + class selection runs in the reconstructor (it needs a
        // mutable arena for the independent refuter); this cheap structural check
        // only routes the shape here.
        ProofFragment::WordEquation
    } else if crate::bv_forall_nonconstant::bv_forall_nonconstant_refutation(arena, assertions)
        .is_some()
    {
        ProofFragment::BvForallNonconstant
    } else if crate::bv_uf_local::bv_uf_local_refutation(arena, assertions).is_some() {
        ProofFragment::BvUfLocal
    } else if has_exists
        && has_forall
        && quant_bv_instance_set_lean::bv_alternation_counterexample_lean_shape(arena, assertions)
    {
        ProofFragment::BvAlternationCounterexample
    } else if (has_exists || has_forall) && finite_domain_enum_certifies(arena, assertions) {
        ProofFragment::FiniteDomainEnum
    } else if has_forall
        && crate::int_reconstruct::int_euclidean_residue_lean_shape(arena, assertions)
    {
        ProofFragment::IntEuclideanResidue
    } else if has_forall && crate::int_reconstruct::int_affine_growth_lean_shape(arena, assertions)
    {
        ProofFragment::IntAffineGrowth
    } else if has_forall
        && crate::quant_nested_xor_cert::int_nested_xor_refutation(arena, assertions).is_some()
    {
        ProofFragment::IntNestedXor
    } else if (has_forall || has_exists)
        && crate::int_reconstruct::single_pivot_equality_partition_lean_shape(arena, assertions)
    {
        ProofFragment::SinglePivotEqualityPartition
    } else if has_exists
        && has_forall
        && quant_bv_instance_set_lean::bv_vacuous_exists_universal_counterexample_lean_shape(
            arena, assertions,
        )
    {
        ProofFragment::BvVacuousExistsUniversalCounterexample
    } else if has_forall
        && quant_bv_instance_set_lean::bv_closed_universal_counterexample_lean_shape(
            arena, assertions,
        )
    {
        ProofFragment::BvClosedUniversalCounterexample
    } else if has_forall
        && crate::int_reconstruct::closed_universal_counterexample_lean_shape(arena, assertions)
    {
        ProofFragment::ClosedUniversalCounterexample
    } else if has_forall
        && crate::int_reconstruct::quantified_counterexample_cover_lean_shape(arena, assertions)
    {
        ProofFragment::QuantifiedCounterexampleCover
    } else if has_forall
        && quant_bv_instance_set_lean::bv_conjunctive_universal_instance_lean_shape(
            arena, assertions,
        )
    {
        ProofFragment::BvConjunctiveUniversalInstance
    } else if has_forall
        && quant_bv_instance_set_lean::bv_positive_universal_instance_set_lean_shape(
            arena, assertions,
        )
    {
        ProofFragment::BvPositiveUniversalInstanceSet
    } else if has_exists
        && quant_bv_instance_set_lean::negated_existential_witness_lean_shape(arena, assertions)
    {
        ProofFragment::NegatedExistentialWitness
    } else if has_exists {
        ProofFragment::Exists
    } else if has_forall {
        ProofFragment::Forall
    } else if crate::datatype_acyclicity::datatype_structural_refutation(arena, assertions)
        .is_some()
    {
        ProofFragment::DatatypeStructural
    } else if has_datatype {
        ProofFragment::Datatype
    } else if crate::set_cardinality::set_cardinality_refutation(arena, assertions).is_some() {
        ProofFragment::SetCardinality
    } else if crate::bv_defined_enum::bv_defined_enum_refutation(arena, assertions).is_some() {
        ProofFragment::BvDefinedEnum
    } else if reflexive_disequality_assertion(arena, assertions).is_some() {
        ProofFragment::ReflexiveDisequality
    } else if crate::term_identity::term_identity_refutation(arena, assertions).is_some() {
        ProofFragment::TermIdentity
    } else if crate::bool_simplify::bool_simplification_refutation(arena, assertions).is_some() {
        ProofFragment::BoolSimplification
    } else if crate::array_axiom::array_axiom_refutation(arena, assertions).is_some() {
        ProofFragment::ArrayAxiom
    } else if crate::abv::const_array_default_mismatch_refutation(arena, assertions).is_some() {
        ProofFragment::ConstArrayDefaultMismatch
    } else if crate::abv::store_chain_readback_refutation(arena, assertions).is_some() {
        ProofFragment::StoreChainReadback
    } else if crate::abv::cross_store_array_disequality_refutation(arena, assertions).is_some() {
        ProofFragment::CrossStoreArrayDisequality
    } else if crate::array_finite::bool_array_read_collapse_refutation(arena, assertions).is_some()
    {
        ProofFragment::BoolArrayReadCollapse
    } else if crate::array_finite::finite_array_extensionality_refutation(arena, assertions)
        .is_some()
    {
        ProofFragment::FiniteArrayExtensionality
    } else if crate::array_bv_abs::bv_abstraction_refutation(arena, assertions).is_some() {
        ProofFragment::BvAbstraction
    } else if crate::array_memcpy::two_byte_memcpy_refutation(arena, assertions).is_some() {
        ProofFragment::TwoByteMemcpy
    } else if crate::array_sort2::two_element_bubble_sort_refutation(arena, assertions).is_some() {
        ProofFragment::TwoElementBubbleSort
    } else if crate::array_sort2::two_element_selection_sort_refutation(arena, assertions).is_some()
    {
        ProofFragment::TwoElementSelectionSort
    } else if crate::array_xor_swap::two_cell_xor_swap_refutation(arena, assertions).is_some() {
        ProofFragment::TwoCellXorSwap
    } else if crate::array_xor_swap::two_byte_xor_swap_roundtrip_refutation(arena, assertions)
        .is_some()
    {
        ProofFragment::TwoByteXorSwapRoundtrip
    } else if crate::array_binary_search::binary_search16_refutation(arena, assertions).is_some() {
        ProofFragment::BinarySearch16
    } else if crate::array_fifo::fifo_bc04_refutation(arena, assertions).is_some() {
        ProofFragment::FifoBc04
    } else if crate::array_write_chain::aligned_write_chain_commutation_refutation(
        arena, assertions,
    )
    .is_some()
    {
        ProofFragment::AlignedWriteChainCommutation
    } else if has_array {
        ProofFragment::QfAbv
    } else if direct::finite_domain_pigeonhole_certifies(arena, assertions) {
        ProofFragment::FiniteDomainPigeonhole
    } else if crate::ufbv_finite::bool_uf_exhaustive_refutation(arena, assertions).is_some() {
        ProofFragment::BoolUfExhaustive
    } else if crate::bool_euf::bool_euf_exhaustive_refutation(arena, assertions).is_some() {
        ProofFragment::BoolEufExhaustive
    } else if crate::bool_euf::bool_euf_online_refutation(arena, assertions).is_some() {
        ProofFragment::BoolEufOnline
    } else if crate::uf_arith::uf_arith_congruence_refutation(arena, assertions).is_some() {
        ProofFragment::UfArithCongruence
    } else if has_func && has_bv {
        ProofFragment::QfUfBv
    } else if has_func && has_arith && arith_dpll_refutation_certifies(arena, assertions) {
        // Boolean-structured UFLIA/UFLRA slices whose UF applications are only
        // needed as opaque arithmetic terms. The ArithDPLL checker re-derives the
        // abstraction refutation before the Lean wrapper is allowed.
        ProofFragment::ArithDpll
    } else if has_func || (has_uninterpreted_sort && !has_arith) {
        ProofFragment::QfUf
    } else if has_arith {
        scan_arithmetic_proof_fragment(arena, assertions)
    } else {
        scan_ground_bv_proof_fragment(arena, assertions)
    }
}

fn scan_arithmetic_proof_fragment(arena: &TermArena, assertions: &[TermId]) -> ProofFragment {
    // The single-square SOS shape (`ℓ*ℓ < 0`, no ring normalizer), the
    // two-variable AM-GM sum form (`x²+y²−2xy < 0`), and any query whose SOS
    // certificate is a single perfect square of a ±1-coefficient linear form
    // (e.g. `(x+y)² < 0`, all driven by the degree-2 ring normalizer) are owned
    // by the dedicated SOS reconstructor; any other arithmetic query falls
    // through to the linear Farkas (LRA) path.
    if is_single_square_lt_zero(arena, assertions).is_some()
        || is_am_gm_two_var(arena, assertions).is_some()
        || is_sos_single_unit_square(arena, assertions)
        || is_sos_multi_unit_square(arena, assertions)
        || is_sos_rational_weight(arena, assertions)
        || is_sos_rational_weight_gt(arena, assertions)
        || sos_certificate_certifies(arena, assertions)
    {
        ProofFragment::Sos
    } else if crate::nra_even_power::nra_even_power_refutation(arena, assertions).is_some() {
        // Higher even-power nonnegativity (e.g. `x^4 < 0`) is outside the
        // degree-2 SOS/LDLᵀ certificate, but has its own checked structural
        // certificate and Lean wrapper.
        ProofFragment::NraEvenPower
    } else if crate::prove_lia_unsat_by_diophantine(arena, assertions) {
        // An integer-equality system that is integer-infeasible (`gcd ∤ const`).
        // Owned by the integer-prelude Diophantine reconstructor (ADR-0042);
        // anything else falls through to the linear Farkas (LRA) path.
        ProofFragment::Diophantine
    } else if crate::is_int_inequality_refutation(arena, assertions) {
        // A single-variable integer-INEQUALITY interval `c ≤ k·x ≤ d` (k > 0)
        // with no multiple of `k` in `[c, d]`: integer-infeasible while
        // LP-feasible. Owned by the integer-prelude inequality reconstructor
        // (ADR-0042); anything else falls through to the linear Farkas path.
        ProofFragment::IntInequality
    } else if is_disjunctive_lra_refutation(arena, assertions) {
        // A conjunctive linear-real system plus exactly one clause `(L₁ ∨ L₂)`
        // of non-strict literals, with each leaf `conj ∧ Lᵢ` Farkas-refutable.
        // Reconstructed by a kernel case-split (`Or.rec`) reusing the per-leaf
        // conjunctive Farkas fold; the purely-conjunctive `Lra` path can never
        // match, so this is uncovered by `reconstruct_lra_proof` today.
        ProofFragment::DisjunctiveLra
    } else if lra_dpll_refutation_certifies(arena, assertions) {
        // General Boolean-structured pure-real LRA. The lazy-SMT certificate is
        // re-derived and self-checked here before Lean reconstruction is allowed.
        ProofFragment::LraDpll
    } else if arith_dpll_refutation_certifies(arena, assertions) {
        // General Boolean-structured linear arithmetic. The arithmetic lazy-SMT
        // certificate is re-derived and self-checked before reconstruction.
        ProofFragment::ArithDpll
    } else if bounded_int_blast_certifies(arena, assertions) {
        // Bounded nonlinear/integer arithmetic whose exact finite-box bit-blast
        // has a re-checkable certificate (box + regenerated DIMACS + DRAT).
        ProofFragment::BoundedIntBlast
    } else {
        ProofFragment::Lra
    }
}

fn lra_dpll_refutation_certifies(arena: &TermArena, assertions: &[TermId]) -> bool {
    let mut scratch = arena.clone();
    matches!(
        crate::dpll_t::certify_lra_dpll_unsat(
            &mut scratch,
            assertions,
            &crate::backend::SolverConfig::default(),
        ),
        Ok(crate::dpll_t::LraDpllOutcome::Unsat(_))
    )
}

fn arith_dpll_refutation_certifies(arena: &TermArena, assertions: &[TermId]) -> bool {
    let mut scratch = arena.clone();
    matches!(
        crate::dpll_lia::certify_arith_dpll_unsat(
            &mut scratch,
            assertions,
            &crate::backend::SolverConfig::default(),
        ),
        Ok(crate::dpll_lia::ArithDpllOutcome::Unsat(_))
    )
}

fn bounded_int_blast_certifies(arena: &TermArena, assertions: &[TermId]) -> bool {
    match crate::auto::certify_bounded_int_blast(arena, assertions) {
        Ok(Some(cert)) => matches!(cert.recheck(arena, assertions), Ok(true)),
        Ok(None) | Err(_) => false,
    }
}

/// Confirm `term` kernel-infers to `False` under `ctx` — the soundness gate shared
/// by every [`prove_unsat_to_lean`] branch that uses a [`ReconstructCtx`].
fn require_infers_false(ctx: &mut ReconstructCtx, term: ExprId) -> Result<(), ReconstructError> {
    let inferred = ctx
        .kernel_mut()
        .infer(term)
        .map_err(|e| ReconstructError::KernelRejected {
            rule: "prove_unsat_to_lean".to_owned(),
            detail: format!("infer failed: {e:?}"),
        })?;
    let false_ = {
        let name = ctx.prelude().false_;
        ctx.kernel_mut().const_(name, vec![])
    };
    if ctx.kernel_mut().def_eq(inferred, false_) {
        Ok(())
    } else {
        Err(ReconstructError::KernelRejected {
            rule: "prove_unsat_to_lean".to_owned(),
            detail: "reconstructed term did not infer to False".to_owned(),
        })
    }
}

/// **The unified Alethe→Lean entry point.** Prove `assertions` UNSAT and reconstruct
/// the refutation to a Lean `False` that the trusted [`Kernel`] accepts, dispatching
/// by [`scan_proof_fragment`] to the matching theory emitter + reconstructor. On
/// success returns the [`ProofFragment`] routed — the proof was both emitted AND
/// kernel-checked to `False`, so a successful return is a machine-checkable refutation
/// of the original assertions across the covered fragments (`QF_BV`/`QF_UF`/`QF_UFBV`/
/// `QF_ABV`, datatypes, `LRA`, and `∀`/`∃` quantifiers).
///
/// # Errors
///
/// [`ReconstructError::UnsupportedRule`] when no reconstructor covers the fragment;
/// [`ReconstructError::MalformedStep`] when the emitter declines (the instance is not
/// UNSAT through that fragment); [`ReconstructError::KernelRejected`] when a
/// reconstruction does not kernel-check to `False`. Never returns a wrong `False`.
pub fn prove_unsat_to_lean(
    arena: &mut TermArena,
    assertions: &[TermId],
) -> Result<ProofFragment, ReconstructError> {
    prove_unsat_to_lean_module(arena, assertions).map(|(fragment, _)| fragment)
}

/// The theorem name used for the exported refutation in a rendered Lean module.
const LEAN_MODULE_THEOREM: &str = "axeyum_refutation";

/// Render the [`ReconstructCtx`]'s kernel state as a self-contained Lean module
/// proving `proof : False` (the shared closing step of the non-LRA branches).
fn render_ctx_module(ctx: &mut ReconstructCtx, proof: ExprId) -> String {
    let false_ = {
        let n = ctx.prelude().false_;
        ctx.kernel_mut().const_(n, vec![])
    };
    ctx.kernel()
        .render_lean_module(LEAN_MODULE_THEOREM, false_, proof)
}

/// Gate a [`LraReconstructCtx`]-built `proof : False` through the kernel
/// (`infer` + `def_eq False`) and render the self-contained Lean module — the
/// shared closing step of the arithmetic branches (`Lra`, `Sos`). `kind` names the
/// fragment in any rejection diagnostic.
fn gate_and_render_lra_module(
    ctx: &mut LraReconstructCtx,
    proof: ExprId,
    kind: &str,
) -> Result<String, ReconstructError> {
    let inferred = ctx
        .kernel_mut()
        .infer(proof)
        .map_err(|e| ReconstructError::KernelRejected {
            rule: "prove_unsat_to_lean".to_owned(),
            detail: format!("infer failed: {e:?}"),
        })?;
    let false_ = {
        let f = ctx.arith().logic.false_;
        ctx.kernel_mut().const_(f, vec![])
    };
    if !ctx.kernel_mut().def_eq(inferred, false_) {
        return Err(ReconstructError::KernelRejected {
            rule: "prove_unsat_to_lean".to_owned(),
            detail: format!("reconstructed {kind} term did not infer to False"),
        });
    }
    Ok(ctx
        .kernel()
        .render_lean_module(LEAN_MODULE_THEOREM, false_, proof))
}

/// Dispatch a `QF_DT` (datatype-fragment) refutation to a self-contained Lean
/// module, trying the four **axiom-free field-axiom** routes in order — is-tester
/// fold, constructor distinctness, constructor injectivity, and **acyclicity**
/// (the occurs-check, the last axiom) — before falling back to the general
/// datatype-simplification → `QF_UFBV` reconstructor. Split out of
/// [`prove_unsat_to_lean_module`] so each arm stays bounded.
///
/// # Errors
///
/// [`ReconstructError`] when no datatype route covers the assertions or a route's
/// reconstruction fails to kernel-check to `False`.
fn dispatch_datatype_to_lean_module(
    arena: &mut TermArena,
    assertions: &[TermId],
) -> Result<String, ReconstructError> {
    // Route-A is-tester fold: a pure `is_C(cⱼ x…)` contradiction is discharged
    // **by ι** (axiom-free over the fold) through the dedicated tester
    // reconstructor; distinctness, injectivity, and acyclicity are the other three
    // datatype field axioms, each discharged axiom-free. Any other datatype proof
    // (select-over-construct, mixed BV residual) falls back to the general QF_UFBV
    // reconstructor, where the read-over-construct projection is itself
    // ι-discharged.
    if let Some(module) = reconstruct_qf_dt_tester_to_lean_module(arena, assertions) {
        module
    } else if let Some(module) = reconstruct_qf_dt_distinct_to_lean_module(arena, assertions) {
        // Constructor DISTINCTNESS `C x = D y` (C ≠ D): ι + congruence + the
        // true≠false discriminator — axiom-free, no `noConfusion`.
        module
    } else if let Some(module) = reconstruct_qf_dt_injective_to_lean_module(arena, assertions) {
        // Constructor INJECTIVITY `C x = C y ∧ ¬(x_i = y_i)` (SAME ctor C): ι
        // (selector-over-construct) + congruence + the field disequality —
        // axiom-free, no `noConfusion`.
        module
    } else if let Some(module) = reconstruct_qf_dt_acyclic_to_lean_module(arena, assertions) {
        // ACYCLICITY (occurs-check) `x = C(… x …)`: the SIZE argument — a
        // `size : D → Nat` recursor gives `size x = Nat.succ (size x)` by
        // congruence + ι, refuted by `n ≠ Nat.succ n` (Nat induction). Axiom-free,
        // no well-founded recursion, no acyclicity axiom. Completes the QF_DT
        // field-axiom Lean chain.
        module
    } else {
        let declined = || ReconstructError::MalformedStep {
            rule: "prove_unsat_to_lean".to_owned(),
            detail: "emitter declined: not unsat through this fragment".to_owned(),
        };
        let p = crate::prove_qf_dt_unsat_alethe_via_simplification(arena, assertions)
            .ok_or_else(declined)?;
        let mut ctx = ReconstructCtx::new();
        let t = reconstruct_qf_ufbv_proof(&mut ctx, &p)?;
        require_infers_false(&mut ctx, t)?;
        Ok(render_ctx_module(&mut ctx, t))
    }
}


/// **Like [`prove_unsat_to_lean`], but also returns a self-contained Lean 4
/// module** (`prelude`-mode source) that re-proves the refutation and can be
/// checked by an independent `lean` binary.
///
/// The string is [`Kernel::render_lean_module`] over the same kernel state the
/// in-tree checker accepted: it declares every reachable constant (logical
/// prelude, carrier, uninterpreted symbols, `em`) and closes with
/// `theorem axeyum_refutation : False := <proof>` plus a `#print axioms` audit.
/// A successful return means the refutation was emitted, kernel-checked to
/// `False`, **and** rendered to externally-checkable Lean source — never a wrong
/// `False`.
///
/// If direct reconstruction declines, the assertion spine is retried after
/// splitting top-level conjunctions and stripping repeated top-level double
/// negations. This accepts consumer-facing shapes such as a single
/// `hyps ∧ ¬goal` assertion without perturbing existing direct routes.
///
/// # Errors
///
/// Same as [`prove_unsat_to_lean`]: an [`ReconstructError`] when no reconstructor
/// covers the fragment, the emitter declines (not UNSAT through that fragment), or
/// a reconstruction fails to kernel-check to `False`.
pub fn prove_unsat_to_lean_module(
    arena: &mut TermArena,
    assertions: &[TermId],
) -> Result<(ProofFragment, String), ReconstructError> {
    let fragment = scan_proof_fragment(arena, assertions);
    match reconstruct_proof_fragment_to_lean_module(fragment, arena, assertions) {
        Ok(source) => Ok((fragment, source)),
        Err(original_error) if should_retry_with_normalized_lean_input(&original_error) => {
            let normalized_assertions = normalize_lean_assertion_inputs(arena, assertions);
            let normalized = normalized_assertions.as_slice();
            if normalized == assertions {
                return Err(original_error);
            }
            let fragment = scan_proof_fragment(arena, normalized);
            let source = reconstruct_proof_fragment_to_lean_module(fragment, arena, normalized)?;
            Ok((fragment, source))
        }
        Err(error) => Err(error),
    }
}

fn should_retry_with_normalized_lean_input(error: &ReconstructError) -> bool {
    matches!(
        error,
        ReconstructError::UnsupportedTerm { .. }
            | ReconstructError::UnsupportedRule { .. }
            | ReconstructError::MalformedStep { .. }
            | ReconstructError::UnsupportedResolution { .. }
    )
}

/// Normalizes the assertion spine accepted by the Lean reconstruction facade.
///
/// Several reconstructors intentionally recognize small, checkable fragments over
/// a slice of top-level facts. Consumer frontends naturally pass the same facts as
/// one `and` tree or wrap a goal negation in `not (not ...)`; both are equivalent
/// to the fact slice under the classical SMT semantics the solver checks. This is
/// used only as a fallback after direct reconstruction declines, so existing
/// route-specific audit behavior is preserved. Keep it deliberately shallow:
/// only the top-level assertion spine is split, and only repeated top-level
/// double negations are removed.
fn normalize_lean_assertion_inputs(arena: &TermArena, assertions: &[TermId]) -> Vec<TermId> {
    let mut normalized = Vec::new();
    for &assertion in assertions {
        collect_normalized_lean_assertion(arena, assertion, &mut normalized);
    }
    normalized
}

fn collect_normalized_lean_assertion(arena: &TermArena, term: TermId, out: &mut Vec<TermId>) {
    let term = strip_top_double_negations(arena, term);
    if let IrTermNode::App {
        op: IrOp::BoolAnd,
        args,
    } = arena.node(term)
        && let [left, right] = &**args
    {
        collect_normalized_lean_assertion(arena, *left, out);
        collect_normalized_lean_assertion(arena, *right, out);
        return;
    }
    out.push(term);
}

fn strip_top_double_negations(arena: &TermArena, mut term: TermId) -> TermId {
    loop {
        let Some(inner) = (match arena.node(term) {
            IrTermNode::App {
                op: IrOp::BoolNot,
                args,
            } => match &**args {
                [inner] => Some(*inner),
                _ => None,
            },
            _ => None,
        }) else {
            return term;
        };
        let Some(grandchild) = (match arena.node(inner) {
            IrTermNode::App {
                op: IrOp::BoolNot,
                args,
            } => match &**args {
                [grandchild] => Some(*grandchild),
                _ => None,
            },
            _ => None,
        }) else {
            return term;
        };
        term = grandchild;
    }
}

#[allow(clippy::too_many_lines)]
fn reconstruct_proof_fragment_to_lean_module(
    fragment: ProofFragment,
    arena: &mut TermArena,
    assertions: &[TermId],
) -> Result<String, ReconstructError> {
    if let Some(source) =
        direct::reconstruct_direct_structural_fragment_to_lean_module(fragment, arena, assertions)?
    {
        return Ok(source);
    }

    let declined = || ReconstructError::MalformedStep {
        rule: "prove_unsat_to_lean".to_owned(),
        detail: "emitter declined: not unsat through this fragment".to_owned(),
    };
    let source = match fragment {
        ProofFragment::QfBv => {
            let p =
                crate::prove_qf_bv_unsat_alethe_lowered(arena, assertions).ok_or_else(declined)?;
            let mut ctx = ReconstructCtx::new();
            let t = reconstruct_qf_bv_proof(&mut ctx, &p)?;
            require_infers_false(&mut ctx, t)?;
            render_ctx_module(&mut ctx, t)
        }
        ProofFragment::QfUf => {
            let p = crate::prove_qf_uf_unsat_alethe(arena, assertions).ok_or_else(declined)?;
            let mut ctx = ReconstructCtx::new();
            let t = reconstruct_qf_uf_proof(&mut ctx, &p)?;
            require_infers_false(&mut ctx, t)?;
            render_ctx_module(&mut ctx, t)
        }
        ProofFragment::QfUfBv => {
            let p = crate::prove_qf_ufbv_unsat_alethe(arena, assertions).ok_or_else(declined)?;
            let mut ctx = ReconstructCtx::new();
            let t = reconstruct_qf_ufbv_proof(&mut ctx, &p)?;
            require_infers_false(&mut ctx, t)?;
            render_ctx_module(&mut ctx, t)
        }
        ProofFragment::ReflexiveDisequality
        | ProofFragment::TermIdentity
        | ProofFragment::BoolSimplification
        | ProofFragment::LraDpll
        | ProofFragment::ArithDpll
        | ProofFragment::BoundedIntBlast
        | ProofFragment::NraEvenPower
        | ProofFragment::FiniteDomainPigeonhole
        | ProofFragment::BoolUfExhaustive
        | ProofFragment::BoolEufExhaustive
        | ProofFragment::BoolEufOnline
        | ProofFragment::UfArithCongruence
        | ProofFragment::DatatypeStructural
        | ProofFragment::FiniteDomainEnum
        | ProofFragment::TermLevelEnum
        | ProofFragment::BvDefinedEnum
        | ProofFragment::SetCardinality
        | ProofFragment::BvForallNonconstant
        | ProofFragment::BvUfLocal
        | ProofFragment::ArrayAxiom
        | ProofFragment::ConstArrayDefaultMismatch
        | ProofFragment::StoreChainReadback
        | ProofFragment::CrossStoreArrayDisequality
        | ProofFragment::BoolArrayReadCollapse
        | ProofFragment::FiniteArrayExtensionality
        | ProofFragment::BvAbstraction
        | ProofFragment::TwoByteMemcpy
        | ProofFragment::TwoElementBubbleSort
        | ProofFragment::TwoElementSelectionSort
        | ProofFragment::TwoCellXorSwap
        | ProofFragment::TwoByteXorSwapRoundtrip
        | ProofFragment::BinarySearch16
        | ProofFragment::FifoBc04
        | ProofFragment::AlignedWriteChainCommutation => {
            unreachable!("direct structural fragments are handled before the general dispatcher")
        }
        ProofFragment::QfAbv => reconstruct_qf_abv_to_lean_source(arena, assertions)?,
        ProofFragment::Datatype => dispatch_datatype_to_lean_module(arena, assertions)?,
        ProofFragment::Forall => {
            let p = crate::prove_quant_unsat_alethe(arena, assertions).ok_or_else(declined)?;
            let mut ctx = ReconstructCtx::new();
            let t = reconstruct_quant_unsat_proof(&mut ctx, &p)?;
            require_infers_false(&mut ctx, t)?;
            render_ctx_module(&mut ctx, t)
        }
        ProofFragment::ClosedUniversalCounterexample => {
            let config = crate::SolverConfig::default()
                .with_timeout(std::time::Duration::from_secs(2))
                .with_resource_limit(1_000_000);
            let certificate =
                crate::quant_closed_counterexample_search::find_closed_universal_counterexample(
                    arena, assertions, &config,
                )
                .map_err(|error| ReconstructError::MalformedStep {
                    rule: "closed_universal_counterexample".to_owned(),
                    detail: format!("counterexample search failed: {error}"),
                })?
                .ok_or_else(declined)?;
            crate::int_reconstruct::reconstruct_closed_universal_counterexample_to_lean_module(
                arena,
                assertions,
                &certificate,
            )?
        }
        ProofFragment::BvClosedUniversalCounterexample => {
            let config = crate::SolverConfig::default()
                .with_timeout(std::time::Duration::from_secs(2))
                .with_resource_limit(1_000_000);
            let certificate =
                crate::quant_closed_counterexample_search::find_closed_universal_counterexample(
                    arena, assertions, &config,
                )
                .map_err(|error| ReconstructError::MalformedStep {
                    rule: "bv_closed_universal_counterexample".to_owned(),
                    detail: format!("counterexample search failed: {error}"),
                })?
                .ok_or_else(declined)?;
            quant_bv_instance_set_lean::reconstruct_bv_closed_universal_counterexample_to_lean_module(
                arena,
                assertions,
                &certificate,
            )?
        }
        ProofFragment::BvVacuousExistsUniversalCounterexample => {
            let config = crate::SolverConfig::default()
                .with_timeout(std::time::Duration::from_secs(2))
                .with_resource_limit(1_000_000);
            let certificate = crate::quant_vacuous_exists_counterexample_search::find_vacuous_exists_universal_counterexample(
                arena,
                assertions,
                &config,
            )
            .map_err(|error| ReconstructError::MalformedStep {
                rule: "bv_vacuous_exists_universal_counterexample".to_owned(),
                detail: format!("counterexample search failed: {error}"),
            })?
            .ok_or_else(declined)?;
            quant_bv_instance_set_lean::reconstruct_bv_vacuous_exists_universal_counterexample_to_lean_module(
                arena,
                assertions,
                &certificate,
            )?
        }
        ProofFragment::BvAlternationCounterexample => {
            let config = crate::SolverConfig::default()
                .with_timeout(std::time::Duration::from_secs(30))
                .with_resource_limit(10_000_000);
            let certificate =
                crate::quant_bv_alternation_search::find_bv_alternation_counterexample(
                    arena, assertions, &config,
                )
                .map_err(|error| ReconstructError::MalformedStep {
                    rule: "bv_alternation_counterexample".to_owned(),
                    detail: format!("counterexample search failed: {error}"),
                })?
                .ok_or_else(declined)?;
            quant_bv_instance_set_lean::reconstruct_bv_alternation_counterexample_to_lean_module(
                arena,
                assertions,
                &certificate,
            )?
        }
        ProofFragment::BvPairedExistentialTransfer => {
            let config = crate::SolverConfig::default()
                .with_timeout(std::time::Duration::from_secs(30))
                .with_resource_limit(10_000_000);
            let certificate =
                crate::quant_bv_paired_exists_search::find_bv_paired_existential_transfer(
                    arena, assertions, &config,
                )
                .map_err(|error| ReconstructError::MalformedStep {
                    rule: "bv_paired_existential_transfer".to_owned(),
                    detail: format!("paired-existential search failed: {error}"),
                })?
                .ok_or_else(declined)?;
            quant_bv_instance_set_lean::reconstruct_bv_paired_existential_transfer_to_lean_module(
                arena,
                assertions,
                &certificate,
            )?
        }
        ProofFragment::IntNestedXor => {
            let certificate =
                crate::quant_nested_xor_cert::int_nested_xor_refutation(arena, assertions)
                    .ok_or_else(declined)?;
            crate::int_reconstruct::reconstruct_int_nested_xor_to_lean_module(
                arena,
                assertions,
                &certificate,
            )?
        }
        ProofFragment::IntEuclideanResidue => {
            let certificate =
                crate::quant_residue_cert::int_euclidean_residue_refutation(arena, assertions)
                    .ok_or_else(declined)?;
            crate::int_reconstruct::reconstruct_int_euclidean_residue_to_lean_module(
                arena,
                assertions,
                &certificate,
            )?
        }
        ProofFragment::IntAffineGrowth => {
            let certificate =
                crate::quant_affine_growth_cert::int_affine_growth_refutation(arena, assertions)
                    .ok_or_else(declined)?;
            crate::int_reconstruct::reconstruct_int_affine_growth_to_lean_module(
                arena,
                assertions,
                &certificate,
            )?
        }
        ProofFragment::SinglePivotEqualityPartition => {
            let certificate =
                crate::quant_eq_partition_search::equality_partition_refutation(arena, assertions)
                    .ok_or_else(declined)?;
            crate::int_reconstruct::reconstruct_single_pivot_equality_partition_to_lean_module(
                arena,
                assertions,
                &certificate,
            )?
        }
        ProofFragment::QuantifiedCounterexampleCover => {
            let config =
                crate::SolverConfig::default().with_timeout(std::time::Duration::from_secs(30));
            let certificate =
                crate::quantified_counterexample_cover_refutation(arena, assertions, &config)
                    .map_err(|error| ReconstructError::MalformedStep {
                        rule: "quantified_counterexample_cover".to_owned(),
                        detail: format!("counterexample-cover search failed: {error}"),
                    })?
                    .ok_or_else(declined)?;
            crate::int_reconstruct::reconstruct_quantified_counterexample_cover_to_lean_module(
                arena,
                assertions,
                &certificate,
            )?
        }
        ProofFragment::BvPositiveUniversalInstanceSet => {
            let config =
                crate::SolverConfig::default().with_timeout(std::time::Duration::from_secs(30));
            let certificate = crate::quant_bool_model_sat::find_bv_positive_universal_instance_set(
                arena, assertions, &config,
            )
            .map_err(|error| ReconstructError::MalformedStep {
                rule: "bv_positive_universal_instance_set".to_owned(),
                detail: format!("instance-set search failed: {error}"),
            })?
            .ok_or_else(declined)?;
            quant_bv_instance_set_lean::reconstruct_bv_positive_universal_instance_set_to_lean_module(
                arena,
                assertions,
                &certificate,
            )?
        }
        ProofFragment::BvConjunctiveUniversalInstance => {
            let config =
                crate::SolverConfig::default().with_timeout(std::time::Duration::from_secs(30));
            let certificate =
                crate::quant_bv_conjunctive_search::find_bv_conjunctive_universal_instance(
                    arena, assertions, &config,
                )
                .map_err(|error| ReconstructError::MalformedStep {
                    rule: "bv_conjunctive_universal_instance".to_owned(),
                    detail: format!("conjunctive-instance search failed: {error}"),
                })?
                .ok_or_else(declined)?;
            quant_bv_instance_set_lean::reconstruct_bv_conjunctive_universal_instance_to_lean_module(
                arena,
                assertions,
                &certificate,
            )?
        }
        ProofFragment::NegatedExistentialWitness => {
            let config =
                crate::SolverConfig::default().with_timeout(std::time::Duration::from_secs(30));
            let certificate = crate::quant_negated_exists_search::find_negated_existential_witness(
                arena, assertions, &config,
            )
            .map_err(|error| ReconstructError::MalformedStep {
                rule: "negated_existential_witness".to_owned(),
                detail: format!("witness search failed: {error}"),
            })?
            .ok_or_else(declined)?;
            quant_bv_instance_set_lean::reconstruct_negated_existential_witness_to_lean_module(
                arena,
                assertions,
                &certificate,
            )?
        }
        ProofFragment::Exists => {
            let cert = crate::prove_skolem_unsat_alethe(arena, assertions).ok_or_else(declined)?;
            let mut ctx = ReconstructCtx::new();
            let t = reconstruct_skolem_unsat_proof(&mut ctx, &cert)?;
            require_infers_false(&mut ctx, t)?;
            render_ctx_module(&mut ctx, t)
        }
        ProofFragment::Lra => {
            let mut ctx = LraReconstructCtx::new();
            let t = reconstruct_lra_proof(&mut ctx, arena, assertions)?;
            gate_and_render_lra_module(&mut ctx, t, "LRA")?
        }
        ProofFragment::DisjunctiveLra => {
            let mut ctx = LraReconstructCtx::new();
            let t = reconstruct_disjunctive_lra_proof(&mut ctx, arena, assertions)?;
            gate_and_render_lra_module(&mut ctx, t, "disjunctive-LRA")?
        }
        ProofFragment::Sos => reconstruct_sos_to_lean_module(arena, assertions)?,
        ProofFragment::Diophantine => {
            // The integer Diophantine reconstructor builds its own integer-prelude
            // kernel, gates the `False` proof, and renders the module (ADR-0042).
            crate::int_reconstruct::reconstruct_diophantine_to_lean_module(arena, assertions)?
        }
        ProofFragment::IntInequality => {
            // The integer-inequality (interval) reconstructor builds its own
            // integer-prelude kernel, gates the `False` proof via discreteness, and
            // renders the module (ADR-0042).
            crate::int_reconstruct::reconstruct_int_inequality_to_lean_module(arena, assertions)?
        }
        ProofFragment::WordEquation => {
            // The word (string/sequence) reconstructor runs the independent refuter,
            // builds its own logic + string prelude kernel, gates the `False` proof,
            // and renders the module (P3.7 strings fragment).
            crate::word_reconstruct::reconstruct_word_clash_to_lean_module(arena, assertions)?
        }
        ProofFragment::Unsupported => {
            return Err(ReconstructError::UnsupportedRule {
                rule: "prove_unsat_to_lean: no reconstructable content".to_owned(),
            });
        }
    };
    Ok(source)
}


fn reconstruct_qf_abv_to_lean_source(
    arena: &mut TermArena,
    assertions: &[TermId],
) -> Result<String, ReconstructError> {
    let declined = || ReconstructError::MalformedStep {
        rule: "prove_unsat_to_lean".to_owned(),
        detail: "emitter declined: not unsat through this fragment".to_owned(),
    };
    if let Some(p) = crate::prove_qf_abv_unsat_alethe(arena, assertions) {
        let mut ctx = ReconstructCtx::new();
        match reconstruct_qf_uf_proof(&mut ctx, &p) {
            Ok(t) => {
                require_infers_false(&mut ctx, t)?;
                return Ok(render_ctx_module(&mut ctx, t));
            }
            Err(direct_error) => {
                let p = crate::prove_qf_abv_unsat_alethe_via_elimination(arena, assertions)
                    .ok_or(direct_error)?;
                let mut ctx = ReconstructCtx::new();
                let t = reconstruct_qf_ufbv_proof(&mut ctx, &p)?;
                require_infers_false(&mut ctx, t)?;
                return Ok(render_ctx_module(&mut ctx, t));
            }
        }
    }
    let p =
        crate::prove_qf_abv_unsat_alethe_via_elimination(arena, assertions).ok_or_else(declined)?;
    let mut ctx = ReconstructCtx::new();
    let t = reconstruct_qf_ufbv_proof(&mut ctx, &p)?;
    require_infers_false(&mut ctx, t)?;
    Ok(render_ctx_module(&mut ctx, t))
}

/// Reconstruct the SOS Lean module for a query the SOS decision proves `unsat`,
/// taking the arena by **shared** reference (the SOS reconstruction reads the query
/// and builds *kernel* terms; it never mutates the IR arena). This is the immutable
/// entry the evidence pipeline ([`crate::produce_nra_sos_evidence`] and
/// `Evidence::check`) calls, since `prove_unsat_to_lean_module`'s `&mut TermArena`
/// is needed only by other fragments.
///
/// # Errors
///
/// Returns a [`ReconstructError`] when the query is not classified as the `Sos`
/// fragment, or the SOS reconstruction does not kernel-check to `False`.
pub fn reconstruct_sos_to_lean_module(
    arena: &TermArena,
    assertions: &[TermId],
) -> Result<String, ReconstructError> {
    match reconstruct_sos_to_lean_module_raw(arena, assertions) {
        Ok(source) => Ok(source),
        Err(original_error) if should_retry_with_normalized_lean_input(&original_error) => {
            let normalized_assertions = normalize_lean_assertion_inputs(arena, assertions);
            let normalized = normalized_assertions.as_slice();
            if normalized == assertions {
                return Err(original_error);
            }
            reconstruct_sos_to_lean_module_raw(arena, normalized)
        }
        Err(error) => Err(error),
    }
}

fn reconstruct_sos_to_lean_module_raw(
    arena: &TermArena,
    assertions: &[TermId],
) -> Result<String, ReconstructError> {
    if scan_proof_fragment(arena, assertions) != ProofFragment::Sos {
        return Err(ReconstructError::MalformedStep {
            rule: "reconstruct_sos_to_lean".to_owned(),
            detail: "query is not an SOS-reconstructable unsat".to_owned(),
        });
    }
    let mut ctx = LraReconstructCtx::new();
    match reconstruct_sos_proof(&mut ctx, arena, assertions) {
        Ok(t) => gate_and_render_lra_module(&mut ctx, t, "SOS"),
        Err(ReconstructError::UnsupportedTerm { .. }) => {
            reconstruct_sos_certificate_wrapper_to_lean_module(arena, assertions)
        }
        Err(error) => Err(error),
    }
}

fn reconstruct_sos_certificate_wrapper_to_lean_module(
    arena: &TermArena,
    assertions: &[TermId],
) -> Result<String, ReconstructError> {
    let cert =
        crate::nra_real_root::sos_refute_with_certificate(arena, assertions).ok_or_else(|| {
            ReconstructError::MalformedStep {
                rule: "sos_certificate".to_owned(),
                detail: "expected a self-checking SOS certificate".to_owned(),
            }
        })?;
    if !cert.verify() {
        return Err(ReconstructError::MalformedStep {
            rule: "sos_certificate".to_owned(),
            detail: "SOS certificate did not verify".to_owned(),
        });
    }

    let mut ctx = ReconstructCtx::new();
    let prop_name = ctx.prop_atom_const("sos_certificate_assertions");
    let prop = ctx.kernel.const_(prop_name, vec![]);
    let asserted = fresh_axiom(&mut ctx, prop, "assume")?;
    let refuter_prop = ctx.mk_not(prop);
    let refuter = fresh_axiom(&mut ctx, refuter_prop, "sos_certificate")?;
    let proof = ctx.kernel.app(refuter, asserted);
    require_infers_false(&mut ctx, proof)?;
    Ok(render_ctx_module(&mut ctx, proof))
}

/// Reconstruct a **complete** EUF `unsat` Alethe proof into a Lean proof term of
/// type `False` that the trusted [`Kernel`] type-checks.
///
/// This walks the `Vec<AletheCommand>` shape that
/// [`crate::prove_qf_uf_unsat_alethe`] emits — `assume` unit clauses (the input
/// equalities/disequalities), self-contained `eq_*`/`eq_congruent` theory clauses,
/// and `resolution` steps threading them — and produces an [`ExprId`] whose
/// inferred type is [`Kernel::def_eq`] to the prelude's `False`. The trusted
/// checker is the gate: a wrong reconstruction makes the final `infer`/`def_eq`
/// fail, so this returns an error, never a wrong `False`.
///
/// ## How each command maps
///
/// - **`assume (cl (= a b))`** ⇒ a fresh axiom `h : Eq α a b` (the input
///   hypothesis as a typed Lean proof).
/// - **`assume (cl (not (= a b)))`** ⇒ a fresh axiom `h : Not (Eq α a b)`
///   (= `Eq α a b → False`).
/// - **`eq_reflexive`/`eq_symmetric`/`eq_transitive`/`eq_congruent`** ⇒ recorded
///   as a Horn theory clause; reconstructed via the slice-1
///   [`reconstruct_eq_step`] (plus `reconstruct_eq_congruent`) when a resolution
///   resolves it against its hypotheses' unit proofs.
/// - **`symm`** (the premise-consuming Alethe flip: premise the unit `(= a b)`,
///   conclusion the unit `(cl (= b a))`) ⇒ reconstructed eagerly via
///   `reconstruct_symm_step` into the swapped unit equality (same `Eq.rec`
///   transport as `eq_symmetric`). Emitted by the congruence-closure fallback.
/// - **`resolution`/`th_resolution`** with a theory clause and its hypotheses'
///   unit proofs ⇒ the reconstructed positive equality unit.
/// - **`resolution`/`th_resolution`** to the empty clause `(cl)` from a positive
///   equality `h_eq : Eq α a b` and its complementary disequality
///   `h_ne : Not (Eq α a b)` ⇒ `h_ne h_eq : False` (the refutation close).
///
/// # Errors
///
/// Returns a [`ReconstructError`] for any out-of-scope command shape, an unknown
/// premise id, a non-Horn/over-arity theory clause, a resolution shape outside
/// this EUF slice, a missing empty-clause derivation, or a kernel rejection. It
/// never panics on malformed or out-of-scope input.
pub fn reconstruct_qf_uf_proof(
    ctx: &mut ReconstructCtx,
    commands: &[AletheCommand],
) -> Result<ExprId, ReconstructError> {
    let mut env: BTreeMap<String, ClauseProof> = BTreeMap::new();

    for cmd in commands {
        match cmd {
            AletheCommand::Assume { id, clause } => {
                let proof = reconstruct_assume(ctx, clause)?;
                env.insert(id.clone(), proof);
            }
            AletheCommand::Step {
                id,
                clause,
                rule,
                premises,
                ..
            } => {
                match rule.as_str() {
                    "eq_reflexive" | "eq_symmetric" | "eq_transitive" | "eq_congruent" => {
                        // A self-contained Horn theory clause; reconstructed lazily.
                        env.insert(
                            id.clone(),
                            ClauseProof::TheoryClause {
                                rule: rule.clone(),
                                clause: clause.clone(),
                            },
                        );
                    }
                    "symm" => {
                        // Premise-consuming flip: one unit-equality premise `(= a b)`
                        // ⊢ the unit `(cl (= b a))`. Reconstruct eagerly into the
                        // swapped `EqUnit`, reusing the `eq_symmetric` `Eq.rec`
                        // transport. (The emitter's congruence-closure fallback flips
                        // an argument-equality unit this way.)
                        let cp = reconstruct_symm_step(ctx, premises, clause, &env)?;
                        env.insert(id.clone(), cp);
                    }
                    "resolution" | "th_resolution" => {
                        let result = reconstruct_resolution(ctx, clause, premises, &env)?;
                        match result {
                            ResolutionResult::Clause(cp) => {
                                env.insert(id.clone(), cp);
                            }
                            ResolutionResult::FalseProof(proof) => {
                                // The empty clause: this is the refutation. Validate
                                // and return it as the final `False` term.
                                return check_false(ctx, proof);
                            }
                        }
                    }
                    other => {
                        return Err(ReconstructError::UnsupportedRule {
                            rule: other.to_owned(),
                        });
                    }
                }
            }
        }
    }

    Err(ReconstructError::NoEmptyClause)
}

/// Reconstruct an `assume` unit clause into a typed hypothesis axiom.
fn reconstruct_assume(
    ctx: &mut ReconstructCtx,
    clause: &[AletheLit],
) -> Result<ClauseProof, ReconstructError> {
    let [lit] = clause else {
        return Err(ReconstructError::UnsupportedResolution {
            detail: format!(
                "this EUF slice only assumes unit clauses; found {} literals",
                clause.len()
            ),
        });
    };
    if let Some((l, r)) = as_positive_eq(lit) {
        // `(= a b)` ⇒ normally a fresh axiom `h : Eq α a b`.
        let le = ctx.alethe_term_to_expr(l)?;
        let re = ctx.alethe_term_to_expr(r)?;
        // **Route-A datatype discharge**: if the two sides are already
        // definitionally equal (`def_eq`) — the read-over-construct case, where the
        // selector application `select_i(C a…)` ι-reduces to its field `a_i` over
        // the kernel inductive — the equation is a *theorem*, proven by `Eq.refl`,
        // NOT an assumed axiom. This is sound for any `def_eq` pair (reflexivity)
        // and is the zero-trust datatype projection: no `fresh_axiom` is minted.
        let proof = if ctx.kernel.def_eq(le, re) {
            ctx.mk_eq_refl(le)
        } else {
            let eq_prop = ctx.mk_eq(le, re);
            fresh_axiom(ctx, eq_prop, "assume")?
        };
        Ok(ClauseProof::EqUnit {
            l: l.clone(),
            r: r.clone(),
            proof,
        })
    } else if let Some((l, r)) = as_negated_eq(lit) {
        // `(not (= a b))` ⇒ a fresh axiom `h : Not (Eq α a b)`.
        let le = ctx.alethe_term_to_expr(l)?;
        let re = ctx.alethe_term_to_expr(r)?;
        let eq_prop = ctx.mk_eq(le, re);
        let not_prop = ctx.mk_not(eq_prop);
        let proof = fresh_axiom(ctx, not_prop, "assume")?;
        Ok(ClauseProof::DiseqUnit {
            l: l.clone(),
            r: r.clone(),
            proof,
        })
    } else {
        Err(ReconstructError::UnsupportedTerm {
            term: lit.atom.key(),
        })
    }
}

/// The outcome of reconstructing a `resolution` step.
enum ResolutionResult {
    /// A reconstructed unit clause (a positive equality or a disequality).
    Clause(ClauseProof),
    /// The empty clause `(cl)` reached: a Lean term of type `False`.
    FalseProof(ExprId),
}

/// Reconstruct a `resolution`/`th_resolution` step over the EUF shapes the emitter
/// produces:
///
/// - **theory-clause resolution**: the first premise is a Horn `eq_*`/`eq_congruent`
///   [`ClauseProof::TheoryClause`]; the remaining premises are unit equality proofs
///   for its negated hypotheses (in any order). Reconstruct the theory clause via the
///   slice-1 helpers with those unit proofs as premises, yielding the positive
///   equality unit.
/// - **closing resolution** (conclusion is the empty clause): a positive equality
///   unit `h_eq : Eq α a b` and its complementary disequality unit
///   `h_ne : Not (Eq α a b)` ⇒ `h_ne h_eq : False`.
fn reconstruct_resolution(
    ctx: &mut ReconstructCtx,
    clause: &[AletheLit],
    premises: &[String],
    env: &BTreeMap<String, ClauseProof>,
) -> Result<ResolutionResult, ReconstructError> {
    // Gather premise reconstructions in order.
    let mut prems: Vec<ClauseProof> = Vec::with_capacity(premises.len());
    for p in premises {
        let cp = env
            .get(p)
            .ok_or_else(|| ReconstructError::UnknownPremise { id: p.clone() })?;
        prems.push(cp.clone());
    }

    // Theory-clause resolution: exactly one TheoryClause premise + unit eq premises.
    if let Some(pos) = prems
        .iter()
        .position(|p| matches!(p, ClauseProof::TheoryClause { .. }))
    {
        let ClauseProof::TheoryClause { rule, clause: tc } = prems[pos].clone() else {
            unreachable!("position matched a TheoryClause");
        };
        // The other premises supply unit proofs for the theory clause's negated
        // hypotheses. Order the unit proofs to match the leading `(not (= …))`
        // literals of the theory clause.
        let mut unit_proofs: Vec<ExprId> = Vec::new();
        for lit in &tc {
            if let Some((hl, hr)) = as_negated_eq(lit) {
                let proof = if let Some(proof) = find_eq_unit(&prems, hl, hr) {
                    proof
                } else if hl == hr {
                    let term = ctx.alethe_term_to_expr(hl)?;
                    ctx.mk_eq_refl(term)
                } else {
                    return Err(ReconstructError::UnsupportedResolution {
                        detail: format!(
                            "no unit equality premise for hypothesis `(= {} {})` of `{rule}`",
                            hl.key(),
                            hr.key()
                        ),
                    });
                };
                unit_proofs.push(proof);
            }
        }
        let proof = match rule.as_str() {
            "eq_congruent" => reconstruct_eq_congruent(ctx, &unit_proofs, &tc)?,
            // The emitter folds a whole chain into ONE `eq_transitive` clause with
            // `k` hypotheses; reconstruct it as a `k`-step transport fold (slice-1's
            // `reconstruct_eq_step` only handles the 2-hypothesis case).
            "eq_transitive" => reconstruct_eq_transitive_n(ctx, &unit_proofs, &tc)?,
            _ => reconstruct_eq_step(ctx, &rule, &unit_proofs, &tc)?,
        };
        // The reconstructed positive equality is the theory clause's last literal.
        let (l, r) = positive_literal(&tc).ok_or_else(|| ReconstructError::MalformedStep {
            rule: rule.clone(),
            detail: "theory clause has no positive equality literal".to_owned(),
        })?;
        return Ok(ResolutionResult::Clause(ClauseProof::EqUnit {
            l: l.clone(),
            r: r.clone(),
            proof,
        }));
    }

    // Closing resolution to the empty clause: a positive eq unit against its
    // complementary disequality unit.
    if clause.is_empty() {
        let proof = close_to_false(ctx, &prems)?;
        return Ok(ResolutionResult::FalseProof(proof));
    }

    Err(ReconstructError::UnsupportedResolution {
        detail: format!(
            "resolution with no theory-clause premise and non-empty conclusion `{}`",
            clause_key(clause)
        ),
    })
}

/// Find the proof of a unit equality `(= l r)` among `prems` (matched
/// structurally on both operands, in the stated orientation).
fn find_eq_unit(prems: &[ClauseProof], l: &AletheTerm, r: &AletheTerm) -> Option<ExprId> {
    prems.iter().find_map(|p| match p {
        ClauseProof::EqUnit {
            l: pl,
            r: pr,
            proof,
        } if pl == l && pr == r => Some(*proof),
        _ => None,
    })
}

/// The two operands of a theory clause's single positive equality literal.
fn positive_literal(clause: &[AletheLit]) -> Option<(&AletheTerm, &AletheTerm)> {
    clause.iter().find_map(as_positive_eq)
}

/// Reconstruct an Alethe `symm` step in the EUF clausal walk: resolve its single
/// premise id to a [`ClauseProof::EqUnit`] `(= a b)` from `env`, build the flipped
/// `(= b a)` proof via [`reconstruct_symm`], and return it as a new unit-equality
/// [`ClauseProof::EqUnit`] with the operands swapped.
fn reconstruct_symm_step(
    ctx: &mut ReconstructCtx,
    premises: &[String],
    clause: &[AletheLit],
    env: &BTreeMap<String, ClauseProof>,
) -> Result<ClauseProof, ReconstructError> {
    let [premise_id] = premises else {
        return Err(ReconstructError::MalformedStep {
            rule: "symm".to_owned(),
            detail: format!("expected exactly one premise, found {}", premises.len()),
        });
    };
    let cp = env
        .get(premise_id)
        .ok_or_else(|| ReconstructError::UnknownPremise {
            id: premise_id.clone(),
        })?;
    let ClauseProof::EqUnit { l, r, proof } = cp else {
        return Err(ReconstructError::MalformedStep {
            rule: "symm".to_owned(),
            detail: "premise is not a positive unit equality `(= a b)`".to_owned(),
        });
    };
    let (l, r, proof) = (l.clone(), r.clone(), *proof);
    let flipped = reconstruct_symm(ctx, &l, &r, proof, clause)?;
    Ok(ClauseProof::EqUnit {
        l: r,
        r: l,
        proof: flipped,
    })
}

/// Close a refutation: among the premises find a positive equality unit
/// `h_eq : Eq α a b` and a complementary disequality unit
/// `h_ne : Not (Eq α a b)` of the **same** equality, and build `h_ne h_eq : False`.
fn close_to_false(
    ctx: &mut ReconstructCtx,
    prems: &[ClauseProof],
) -> Result<ExprId, ReconstructError> {
    for p in prems {
        let ClauseProof::DiseqUnit {
            l: nl,
            r: nr,
            proof: ne_proof,
        } = p
        else {
            continue;
        };
        // Find the matching positive equality `Eq α nl nr`.
        let eq_proof = prems.iter().find_map(|q| match q {
            ClauseProof::EqUnit {
                l: el,
                r: er,
                proof,
            } if el == nl && er == nr => Some(*proof),
            _ => None,
        });
        if let Some(eq_proof) = eq_proof {
            // `h_ne h_eq : False` — Not (Eq α a b) whnf-unfolds to Eq α a b → False.
            let app = ctx.kernel.app(*ne_proof, eq_proof);
            return Ok(app);
        }
    }
    Err(ReconstructError::UnsupportedResolution {
        detail: "closing resolution has no complementary equality/disequality unit pair".to_owned(),
    })
}

/// The soundness gate for the final refutation term: `infer` it and require the
/// inferred type to be [`Kernel::def_eq`] to the prelude's `False`.
fn check_false(ctx: &mut ReconstructCtx, proof: ExprId) -> Result<ExprId, ReconstructError> {
    let false_ = ctx.kernel.const_(ctx.prelude.false_, vec![]);
    check_against(ctx, "resolution", proof, false_)
}

/// Render a clause as a stable diagnostic key.
fn clause_key(clause: &[AletheLit]) -> String {
    let mut out = String::from("(cl");
    for lit in clause {
        out.push(' ');
        if lit.negated {
            out.push_str("(not ");
            out.push_str(&lit.atom.key());
            out.push(')');
        } else {
            out.push_str(&lit.atom.key());
        }
    }
    out.push(')');
    out
}

impl ReconstructCtx {
    /// Build the Lean proposition `Not p` (the prelude's `Not`, which unfolds to
    /// `p → False`).
    fn mk_not(&mut self, p: ExprId) -> ExprId {
        let not = self.kernel.const_(self.prelude.not, vec![]);
        self.kernel.app(not, p)
    }
}

/// Parse a route-A **datatype constructor** head `!dtcon_<n>_<ctorname>`, where
/// `<n>` is the constructor arity. Returns `(arity, ctorname)`, or [`None`] for
/// any non-`!dtcon_` head or a malformed arity. The constructor name may itself
/// contain `_`, so only the leading numeric segment is parsed as the arity.
fn parse_dtcon(head: &str) -> Option<(usize, &str)> {
    let rest = head.strip_prefix("!dtcon_")?;
    let (arity_str, ctor) = rest.split_once('_')?;
    let arity = arity_str.parse::<usize>().ok()?;
    Some((arity, ctor))
}

/// Parse a route-A **datatype selector** head `!dtsel_<n>_<i>_<ctorname>`, where
/// `<n>` is the constructor arity and `<i>` the selected field index. Returns
/// `(arity, index, ctorname)`, or [`None`] for a non-`!dtsel_` head or a
/// malformed arity/index. The constructor name may contain `_`; only the two
/// leading numeric segments are parsed.
fn parse_dtsel(head: &str) -> Option<(usize, usize, &str)> {
    let rest = head.strip_prefix("!dtsel_")?;
    let (arity_str, rest) = rest.split_once('_')?;
    let (index_str, ctor) = rest.split_once('_')?;
    let arity = arity_str.parse::<usize>().ok()?;
    let index = index_str.parse::<usize>().ok()?;
    if index >= arity {
        return None;
    }
    Some((arity, index, ctor))
}

/// The datatype-inductive registry key `"<arity>_<ctorname>"` shared by a
/// constructor `!dtcon_n_c` and all its selectors `!dtsel_n_i_c`, so they map to
/// one kernel inductive.
fn datatype_key(head: &str) -> Option<String> {
    if let Some((arity, ctor)) = parse_dtcon(head) {
        return Some(format!("{arity}_{ctor}"));
    }
    if let Some((arity, _index, ctor)) = parse_dtsel(head) {
        return Some(format!("{arity}_{ctor}"));
    }
    None
}

/// Declare a fresh axiom of proposition `prop` and return a `Const` proof of it.
fn fresh_axiom(
    ctx: &mut ReconstructCtx,
    prop: ExprId,
    role: &str,
) -> Result<ExprId, ReconstructError> {
    let name = ctx.fresh_name("hyp");
    ctx.kernel
        .add_declaration(Declaration::Axiom {
            name,
            uparams: vec![],
            ty: prop,
        })
        .map_err(|e| ReconstructError::KernelRejected {
            rule: role.to_owned(),
            detail: format!("hypothesis axiom did not admit: {e:?}"),
        })?;
    ctx.axiom_roles.insert(name, role.to_owned());
    Ok(ctx.kernel.const_(name, vec![]))
}


#[cfg(test)]
mod tests;
