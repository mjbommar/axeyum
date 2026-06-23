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

use std::collections::{BTreeMap, BTreeSet};

use axeyum_cnf::{AletheCommand, AletheLit, AletheTerm};
use axeyum_lean_kernel::{
    BinderInfo, DatatypeFamily, DatatypeInductive, Declaration, ExprId, ExprNode, Kernel, LevelId,
    LogicPrelude, NameId, build_logic_prelude,
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

/// The reconstruction context: a [`Kernel`] seeded with the logical prelude, the
/// EUF carrier sort `α : Type`, and a deterministic map from Alethe atom/function
/// names to their interned constant [`NameId`].
///
/// Atom constants have type `α`; an arity-`n` function constant has type
/// `α → … → α` (`n` arrows). Declarations are added to the kernel's environment
/// lazily, the first time an atom/function name is seen.
pub struct ReconstructCtx {
    kernel: Kernel,
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
    /// Memoization for [`ReconstructCtx::gate_term_to_prop`]: `AletheTerm` key → its
    /// `Prop` `ExprId`. The bit-blast gates (esp. lowered multipliers/dividers) repeat
    /// shared subterms heavily; without this the CNF-intro rules rebuild them every
    /// time. **Cleared on any `bridge` change** (the result depends on the bridge).
    gate_memo: BTreeMap<String, ExprId>,
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
            gate_memo: BTreeMap::new(),
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

/// Reconstruct an equality-rule step into a kernel-checked Lean proof term.
///
/// `premises` are the proof terms (already-built Lean [`ExprId`]s) for the step's
/// premises, in order; `conclusion` is the step's conclusion **clause** (the
/// step's `(cl …)` literals). The returned proof term is `infer`-checked by the
/// kernel and [`Kernel::def_eq`]-compared to the translated conclusion
/// proposition; on success the proof term is returned.
///
/// Supported `rule`s (this slice):
///
/// - `eq_reflexive` ⊢ `(cl (= a a))` ⇒ `Eq.refl.{1} α a` (no premises);
/// - `eq_symmetric` ⊢ `(cl (not (= a b)) (= b a))`, premise `h : Eq α a b`
///   ⇒ `Eq.rec` transport with motive `fun x _ => Eq α x a`;
/// - `eq_transitive` ⊢ `(cl (not (= a b)) (not (= b c)) (= a c))`, premises
///   `h1 : Eq α a b`, `h2 : Eq α b c` ⇒ `Eq.rec` transport of `h1` along `h2`
///   with motive `fun x _ => Eq α a x`.
///
/// Note the Alethe `eq_*` conclusion clauses carry the **negated hypotheses**
/// inline (`(not (= a b))`); the *positive* equality is the last literal. For
/// reconstruction we extract that positive equality (the actual proposition the
/// rule proves) and the hypothesis equalities from the leading negated literals,
/// rather than treating `premises` as already-clausal — so a self-contained
/// `eq_symmetric`/`eq_transitive` step (premise-free in Alethe) is reconstructed
/// by reading its own clause, while a step threaded with explicit premise proofs
/// supplies those proofs through `premises`.
///
/// # Errors
///
/// Returns [`ReconstructError::UnsupportedRule`] for a non-equality rule,
/// [`ReconstructError::UnsupportedTerm`] for an out-of-scope conclusion term,
/// [`ReconstructError::MalformedStep`] for a clause/premise shape that does not
/// match the rule, and [`ReconstructError::KernelRejected`] when the kernel's
/// `infer` fails or the inferred proposition is not `def_eq` to the conclusion.
pub fn reconstruct_eq_step(
    ctx: &mut ReconstructCtx,
    rule: &str,
    premises: &[ExprId],
    conclusion: &[AletheLit],
) -> Result<ExprId, ReconstructError> {
    match rule {
        "eq_reflexive" => reconstruct_eq_reflexive(ctx, conclusion),
        "eq_symmetric" => reconstruct_eq_symmetric(ctx, premises, conclusion),
        "eq_transitive" => reconstruct_eq_transitive(ctx, premises, conclusion),
        other => Err(ReconstructError::UnsupportedRule {
            rule: other.to_owned(),
        }),
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

/// `eq_reflexive` ⊢ `(cl (= a a))` ⇒ `Eq.refl.{1} α a`.
fn reconstruct_eq_reflexive(
    ctx: &mut ReconstructCtx,
    conclusion: &[AletheLit],
) -> Result<ExprId, ReconstructError> {
    let [lit] = conclusion else {
        return Err(ReconstructError::MalformedStep {
            rule: "eq_reflexive".to_owned(),
            detail: format!("expected one literal, found {}", conclusion.len()),
        });
    };
    let Some((a_t, b_t)) = as_positive_eq(lit) else {
        return Err(ReconstructError::MalformedStep {
            rule: "eq_reflexive".to_owned(),
            detail: "conclusion is not a positive equality `(= a a)`".to_owned(),
        });
    };
    if a_t != b_t {
        return Err(ReconstructError::MalformedStep {
            rule: "eq_reflexive".to_owned(),
            detail: "reflexivity conclusion `(= a b)` has a != b".to_owned(),
        });
    }
    let a = ctx.alethe_term_to_expr(a_t)?;
    let proof = ctx.mk_eq_refl(a);
    let expected = ctx.mk_eq(a, a);
    check_against(ctx, "eq_reflexive", proof, expected)
}

/// `eq_symmetric` ⊢ `(cl (not (= a b)) (= b a))` with premise `h : Eq α a b`
/// ⇒ `Eq.rec.{0,1} α a (fun x _ => Eq α x a) (Eq.refl α a) b h : Eq α b a`.
fn reconstruct_eq_symmetric(
    ctx: &mut ReconstructCtx,
    premises: &[ExprId],
    conclusion: &[AletheLit],
) -> Result<ExprId, ReconstructError> {
    // Conclusion clause: `(not (= a b)) (= b a)`.
    let [hyp, concl] = conclusion else {
        return Err(ReconstructError::MalformedStep {
            rule: "eq_symmetric".to_owned(),
            detail: format!("expected two literals, found {}", conclusion.len()),
        });
    };
    let (Some((a_t, b_t)), Some((c_t, d_t))) = (as_negated_eq(hyp), as_positive_eq(concl)) else {
        return Err(ReconstructError::MalformedStep {
            rule: "eq_symmetric".to_owned(),
            detail: "expected `(cl (not (= a b)) (= b a))`".to_owned(),
        });
    };
    // The conclusion `(= b a)` must swap the hypothesis `(= a b)`.
    if a_t != d_t || b_t != c_t {
        return Err(ReconstructError::MalformedStep {
            rule: "eq_symmetric".to_owned(),
            detail: "conclusion is not the swapped hypothesis".to_owned(),
        });
    }

    let a = ctx.alethe_term_to_expr(a_t)?;
    let b = ctx.alethe_term_to_expr(b_t)?;

    // The premise proof of `Eq α a b`. If an explicit premise term was threaded
    // in, use it; otherwise build the hypothesis as a fresh axiom `h : Eq α a b`
    // so the step is self-contained.
    let h = premise_or_axiom(ctx, premises, 0, a, b, "eq_symmetric")?;

    // motive := fun (x : α) (_ : Eq α a x) => Eq α x a.
    //   Under binders x, hx (innermost = BVar 0): in the body `Eq α x a`,
    //   x = BVar 1; in the hx domain `Eq α a x`, x = BVar 0.
    let motive = {
        let x1 = ctx.kernel.bvar(1);
        let eq_x_a = ctx.mk_eq(x1, a);
        let x0 = ctx.kernel.bvar(0);
        let eq_a_x = ctx.mk_eq(a, x0);
        let anon = ctx.kernel.anon();
        let inner = ctx.kernel.lam(anon, eq_a_x, eq_x_a, BinderInfo::Default);
        ctx.kernel.lam(anon, ctx.alpha, inner, BinderInfo::Default)
    };
    // refl_case : motive a (Eq.refl α a) = Eq α a a, proved by `Eq.refl α a`.
    let refl_case = ctx.mk_eq_refl(a);
    // Eq.rec α a motive refl_case b h  :  motive b h  =  Eq α b a.
    let proof = ctx.mk_eq_rec_transport(a, motive, refl_case, b, h);

    let expected = ctx.mk_eq(b, a);
    check_against(ctx, "eq_symmetric", proof, expected)
}

/// Reconstruct the Alethe `symm` rule: one premise `h : Eq α a b`, conclusion
/// `(cl (= b a))`.
///
/// Unlike the clause-form `eq_symmetric` tautology (`(cl (not (= a b)) (= b a))`,
/// premise-free), `symm` is a *premise-consuming* step: it takes the prior unit
/// equality proof and concludes the flipped unit equality. The mathematical
/// content is identical, so the proof term is the same `Eq.rec` transport as
/// [`reconstruct_eq_symmetric`] (motive `fun x _ => Eq α x a`, refl-case
/// `Eq.refl α a`), built over the premise's operands.
///
/// Returns the swapped operands `(b, a)` alongside the kernel-checked proof so the
/// caller can record the resulting `(= b a)` unit.
///
/// # Errors
///
/// [`ReconstructError::MalformedStep`] when the conclusion is not a single positive
/// equality `(cl (= b a))` swapping the premise's `(= a b)`, and
/// [`ReconstructError::KernelRejected`] through the [`check_against`] gate.
fn reconstruct_symm(
    ctx: &mut ReconstructCtx,
    premise_l: &AletheTerm,
    premise_r: &AletheTerm,
    premise_proof: ExprId,
    conclusion: &[AletheLit],
) -> Result<ExprId, ReconstructError> {
    // Conclusion clause: the single positive `(= b a)`.
    let [concl] = conclusion else {
        return Err(ReconstructError::MalformedStep {
            rule: "symm".to_owned(),
            detail: format!("expected one literal, found {}", conclusion.len()),
        });
    };
    let Some((c_t, d_t)) = as_positive_eq(concl) else {
        return Err(ReconstructError::MalformedStep {
            rule: "symm".to_owned(),
            detail: "conclusion is not a positive equality `(= b a)`".to_owned(),
        });
    };
    // The conclusion `(= b a)` must swap the premise `(= a b)`.
    if c_t != premise_r || d_t != premise_l {
        return Err(ReconstructError::MalformedStep {
            rule: "symm".to_owned(),
            detail: "conclusion is not the swapped premise equality".to_owned(),
        });
    }

    let a = ctx.alethe_term_to_expr(premise_l)?;
    let b = ctx.alethe_term_to_expr(premise_r)?;

    // Same `Eq.rec` transport as `eq_symmetric`: motive `fun x _ => Eq α x a`,
    // refl-case `Eq.refl α a`, transported along `premise_proof : Eq α a b`.
    let motive = {
        let x1 = ctx.kernel.bvar(1);
        let eq_x_a = ctx.mk_eq(x1, a);
        let x0 = ctx.kernel.bvar(0);
        let eq_a_x = ctx.mk_eq(a, x0);
        let anon = ctx.kernel.anon();
        let inner = ctx.kernel.lam(anon, eq_a_x, eq_x_a, BinderInfo::Default);
        ctx.kernel.lam(anon, ctx.alpha, inner, BinderInfo::Default)
    };
    let refl_case = ctx.mk_eq_refl(a);
    let proof = ctx.mk_eq_rec_transport(a, motive, refl_case, b, premise_proof);

    let expected = ctx.mk_eq(b, a);
    check_against(ctx, "symm", proof, expected)
}

/// `eq_transitive` ⊢ `(cl (not (= a b)) (not (= b c)) (= a c))` with premises
/// `h1 : Eq α a b`, `h2 : Eq α b c`
/// ⇒ `Eq.rec.{0,1} α b (fun x _ => Eq α a x) h1 c h2 : Eq α a c`.
fn reconstruct_eq_transitive(
    ctx: &mut ReconstructCtx,
    premises: &[ExprId],
    conclusion: &[AletheLit],
) -> Result<ExprId, ReconstructError> {
    // Conclusion clause: `(not (= a b)) (not (= b c)) (= a c)`.
    let [hyp1, hyp2, concl] = conclusion else {
        return Err(ReconstructError::MalformedStep {
            rule: "eq_transitive".to_owned(),
            detail: format!(
                "this slice reconstructs a single 2-hypothesis chain; found {} literals",
                conclusion.len()
            ),
        });
    };
    let (Some((a_t, b_t)), Some((b2_t, c_t)), Some((ca_t, cc_t))) = (
        as_negated_eq(hyp1),
        as_negated_eq(hyp2),
        as_positive_eq(concl),
    ) else {
        return Err(ReconstructError::MalformedStep {
            rule: "eq_transitive".to_owned(),
            detail: "expected `(cl (not (= a b)) (not (= b c)) (= a c))`".to_owned(),
        });
    };
    // The chain must connect: b_t == b2_t, and the conclusion endpoints a, c.
    if b_t != b2_t || a_t != ca_t || c_t != cc_t {
        return Err(ReconstructError::MalformedStep {
            rule: "eq_transitive".to_owned(),
            detail: "chain links/conclusion endpoints do not match".to_owned(),
        });
    }

    let a = ctx.alethe_term_to_expr(a_t)?;
    let b = ctx.alethe_term_to_expr(b_t)?;
    let c = ctx.alethe_term_to_expr(c_t)?;

    let h1 = premise_or_axiom(ctx, premises, 0, a, b, "eq_transitive")?;
    let h2 = premise_or_axiom(ctx, premises, 1, b, c, "eq_transitive")?;

    // Transport `h1 : Eq α a b` along `h2 : Eq α b c` to `Eq α a c`, recursing on
    // `h2` (fixed left = b).
    // motive := fun (x : α) (_ : Eq α b x) => Eq α a x.
    //   Body `Eq α a x`: x = BVar 1; hx domain `Eq α b x`: x = BVar 0.
    let motive = {
        let x1 = ctx.kernel.bvar(1);
        let eq_a_x = ctx.mk_eq(a, x1);
        let x0 = ctx.kernel.bvar(0);
        let eq_b_x = ctx.mk_eq(b, x0);
        let anon = ctx.kernel.anon();
        let inner = ctx.kernel.lam(anon, eq_b_x, eq_a_x, BinderInfo::Default);
        ctx.kernel.lam(anon, ctx.alpha, inner, BinderInfo::Default)
    };
    // refl_case : motive b (Eq.refl α b) = Eq α a b, proved by `h1`.
    let refl_case = h1;
    // Eq.rec α b motive h1 c h2  :  motive c h2  =  Eq α a c.
    let proof = ctx.mk_eq_rec_transport(b, motive, refl_case, c, h2);

    let expected = ctx.mk_eq(a, c);
    check_against(ctx, "eq_transitive", proof, expected)
}

/// Fetch the `idx`-th premise proof term, or — when no explicit premise was
/// supplied — synthesize a fresh hypothesis axiom `h : Eq α l r` so that a
/// self-contained Alethe `eq_*` step (whose hypotheses live inline in its
/// conclusion clause) is still reconstructible. The synthesized axiom is a
/// genuine kernel `Const` of the exact `Eq α l r` proposition, so the proof
/// term it feeds is well-typed.
fn premise_or_axiom(
    ctx: &mut ReconstructCtx,
    premises: &[ExprId],
    idx: usize,
    l: ExprId,
    r: ExprId,
    rule: &str,
) -> Result<ExprId, ReconstructError> {
    if let Some(&p) = premises.get(idx) {
        return Ok(p);
    }
    if !premises.is_empty() {
        // Some premises were supplied but not enough — that is a real mismatch.
        return Err(ReconstructError::MalformedStep {
            rule: rule.to_owned(),
            detail: format!("missing premise #{idx}"),
        });
    }
    // Premise-free Alethe step: model the inline hypothesis as an axiom.
    let eq_prop = ctx.mk_eq(l, r);
    let name = ctx.fresh_name("hyp");
    ctx.kernel
        .add_declaration(Declaration::Axiom {
            name,
            uparams: vec![],
            ty: eq_prop,
        })
        .map_err(|e| ReconstructError::KernelRejected {
            rule: rule.to_owned(),
            detail: format!("hypothesis axiom did not admit: {e:?}"),
        })?;
    Ok(ctx.kernel.const_(name, vec![]))
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
    let inferred = ctx
        .kernel
        .infer(proof)
        .map_err(|e| ReconstructError::KernelRejected {
            rule: rule.to_owned(),
            detail: format!("infer failed: {e:?}"),
        })?;
    if ctx.kernel.def_eq(inferred, expected) {
        Ok(proof)
    } else {
        Err(ReconstructError::KernelRejected {
            rule: rule.to_owned(),
            detail: "inferred proposition is not def-eq to the conclusion".to_owned(),
        })
    }
}

/// Reconstruct an **n-ary** `eq_congruent` step into a kernel-checked proof term.
///
/// `eq_congruent` ⊢ `(cl (not (= a1 b1)) … (not (= an bn)) (= (f a1…an) (f b1…bn)))`
/// with premises `h_i : Eq α a_i b_i` proves the congruence of an arity-`n`
/// uninterpreted function `f`. Reconstruction transports one argument at a time:
/// starting from `Eq.refl α (f a…)`, each `h_i` drives an `Eq.rec` over the motive
/// `fun (x : α) (_ : Eq α a_i x) => Eq α (f a…) (f a1…a_{i-1} x b_{i+1}…)` (the
/// running accumulator is exactly that step's refl-case), ending at
/// `Eq α (f a1…an) (f b1…bn)`. The unary `f(a)=f(b)` shape is the `n = 1` case.
///
/// # Errors
///
/// Returns [`ReconstructError::MalformedStep`] for a clause whose literals are not
/// `(cl (not (= a1 b1)) … (not (= an bn)) (= (f a1…an) (f b1…bn)))` with matching
/// head/arity/arguments, and [`ReconstructError::UnsupportedRule`] when the
/// conclusion sides are not function applications; the kernel gate fires through
/// [`ReconstructError::KernelRejected`].
fn reconstruct_eq_congruent(
    ctx: &mut ReconstructCtx,
    premises: &[ExprId],
    conclusion: &[AletheLit],
) -> Result<ExprId, ReconstructError> {
    // `(cl (not (= a1 b1)) … (not (= an bn)) (= (f a1…an) (f b1…bn)))`: a leading
    // negated equality per argument, then the positive application equality.
    let Some((concl, hyp_lits)) = conclusion.split_last() else {
        return Err(ReconstructError::MalformedStep {
            rule: "eq_congruent".to_owned(),
            detail: "empty conclusion clause".to_owned(),
        });
    };
    let Some((fa_t, fb_t)) = as_positive_eq(concl) else {
        return Err(ReconstructError::MalformedStep {
            rule: "eq_congruent".to_owned(),
            detail: "last literal is not the positive `(= (f a…) (f b…))` conclusion".to_owned(),
        });
    };
    let (Some((f1, a_args)), Some((f2, b_args))) = (as_nary_app(fa_t), as_nary_app(fb_t)) else {
        return Err(ReconstructError::UnsupportedRule {
            rule: "eq_congruent (conclusion sides are not function applications)".to_owned(),
        });
    };
    if f1 != f2 || a_args.len() != b_args.len() || a_args.len() != hyp_lits.len() {
        return Err(ReconstructError::MalformedStep {
            rule: "eq_congruent".to_owned(),
            detail: "head, arity, or hypothesis count mismatch".to_owned(),
        });
    }
    let arity = a_args.len();
    // Each hypothesis `i` is `(not (= a_i b_i))` for the i-th application argument.
    for (i, lit) in hyp_lits.iter().enumerate() {
        let Some((a_i, b_i)) = as_negated_eq(lit) else {
            return Err(ReconstructError::MalformedStep {
                rule: "eq_congruent".to_owned(),
                detail: "hypothesis is not a negated equality".to_owned(),
            });
        };
        if a_i != &a_args[i] || b_i != &b_args[i] {
            return Err(ReconstructError::MalformedStep {
                rule: "eq_congruent".to_owned(),
                detail: "hypothesis argument does not match the application argument".to_owned(),
            });
        }
    }

    let a_exprs: Vec<ExprId> = a_args
        .iter()
        .map(|t| ctx.alethe_term_to_expr(t))
        .collect::<Result<_, _>>()?;
    let b_exprs: Vec<ExprId> = b_args
        .iter()
        .map(|t| ctx.alethe_term_to_expr(t))
        .collect::<Result<_, _>>()?;
    let f_name = ctx.func_const(f1, arity);

    // Transport one argument at a time: `acc : Eq α (f a…) (f current)`, where
    // `current` starts as `a…` and position `i` is rewritten `a_i → b_i` each step.
    // The previous `acc` is exactly `motive_i a_i (refl)` (`current[i]` is still
    // `a_i`), so it serves as the Eq.rec refl-case.
    let fa = ctx.apply_func(f_name, &a_exprs);
    let mut acc = ctx.mk_eq_refl(fa);
    let mut current = a_exprs.clone();
    for i in 0..arity {
        // h_i : Eq α a_i b_i (explicit premise or self-contained inline axiom).
        let h = premise_or_axiom(ctx, premises, i, a_exprs[i], b_exprs[i], "eq_congruent")?;
        // motive := fun (x : α) (_ : Eq α a_i x) => Eq α (f a…) (f current[i := x]).
        //   Body: x = BVar 1; Eq-domain `Eq α a_i x`: x = BVar 0.
        let motive = {
            let x1 = ctx.kernel.bvar(1);
            let rhs = ctx.apply_func_with_hole(f_name, &current, i, x1);
            let eq_body = ctx.mk_eq(fa, rhs);
            let x0 = ctx.kernel.bvar(0);
            let eq_dom = ctx.mk_eq(a_exprs[i], x0);
            let anon = ctx.kernel.anon();
            let inner = ctx.kernel.lam(anon, eq_dom, eq_body, BinderInfo::Default);
            ctx.kernel.lam(anon, ctx.alpha, inner, BinderInfo::Default)
        };
        // Eq.rec α a_i motive acc b_i h : Eq α (f a…) (f current[i := b_i]).
        acc = ctx.mk_eq_rec_transport(a_exprs[i], motive, acc, b_exprs[i], h);
        current[i] = b_exprs[i];
    }

    // acc : Eq α (f a1…an) (f b1…bn).
    let fb = ctx.apply_func(f_name, &b_exprs);
    let expected = ctx.mk_eq(fa, fb);
    check_against(ctx, "eq_congruent", acc, expected)
}

/// Reconstruct an **n-hypothesis** `eq_transitive` chain into a kernel-checked
/// proof term. The emitter folds a whole equality chain into a single
/// `eq_transitive` clause `(cl (not (= x0 x1)) … (not (= x_{k-1} xk)) (= x0 xk))`,
/// so the 2-hypothesis [`reconstruct_eq_transitive`] is not enough.
///
/// With ordered premise proofs `premises[i] : Eq α x_i x_{i+1}` (in clause order),
/// fold from the left: `acc : Eq α x0 x_{i}` is transported along
/// `premises[i] : Eq α x_i x_{i+1}` (motive `fun y _ => Eq α x0 y`) to
/// `Eq α x0 x_{i+1}`, ending at `Eq α x0 xk`.
///
/// # Errors
///
/// Returns [`ReconstructError::MalformedStep`] for a clause whose `k` leading
/// negated literals do not form a consecutive chain ending at the positive
/// conclusion `(= x0 xk)`, or a premise count that does not match the chain
/// length; [`ReconstructError::KernelRejected`] on the kernel gate.
fn reconstruct_eq_transitive_n(
    ctx: &mut ReconstructCtx,
    premises: &[ExprId],
    conclusion: &[AletheLit],
) -> Result<ExprId, ReconstructError> {
    // Split into the leading negated chain links and the trailing positive concl.
    let Some((concl, links)) = conclusion.split_last() else {
        return Err(ReconstructError::MalformedStep {
            rule: "eq_transitive".to_owned(),
            detail: "empty conclusion clause".to_owned(),
        });
    };
    let Some((c0_t, ck_t)) = as_positive_eq(concl) else {
        return Err(ReconstructError::MalformedStep {
            rule: "eq_transitive".to_owned(),
            detail: "last literal is not the positive `(= x0 xk)` conclusion".to_owned(),
        });
    };
    if links.is_empty() || premises.len() != links.len() {
        return Err(ReconstructError::MalformedStep {
            rule: "eq_transitive".to_owned(),
            detail: format!(
                "chain has {} links but {} premise proofs",
                links.len(),
                premises.len()
            ),
        });
    }

    // Collect the chain nodes `x0, x1, …, xk` from the consecutive negated links,
    // checking that each link starts where the previous ended.
    let mut nodes: Vec<&AletheTerm> = Vec::with_capacity(links.len() + 1);
    for (i, lit) in links.iter().enumerate() {
        let Some((l, r)) = as_negated_eq(lit) else {
            return Err(ReconstructError::MalformedStep {
                rule: "eq_transitive".to_owned(),
                detail: format!("link {i} is not a negated equality `(not (= _ _))`"),
            });
        };
        if i == 0 {
            nodes.push(l);
        } else if nodes[i] != l {
            return Err(ReconstructError::MalformedStep {
                rule: "eq_transitive".to_owned(),
                detail: format!("chain break: link {i} does not start at the previous endpoint"),
            });
        }
        nodes.push(r);
    }
    // Endpoints must match the conclusion `(= x0 xk)`.
    if nodes[0] != c0_t || nodes[nodes.len() - 1] != ck_t {
        return Err(ReconstructError::MalformedStep {
            rule: "eq_transitive".to_owned(),
            detail: "chain endpoints do not match the conclusion".to_owned(),
        });
    }

    // x0 is the fixed left operand of the accumulated equality.
    let x0 = ctx.alethe_term_to_expr(nodes[0])?;
    // acc : Eq α x0 x1  (the first premise proof).
    let mut acc = premises[0];
    // Fold links 1..k: transport acc : Eq α x0 x_i along premises[i] : Eq α x_i x_{i+1}.
    for i in 1..links.len() {
        let xi = ctx.alethe_term_to_expr(nodes[i])?;
        let xi1 = ctx.alethe_term_to_expr(nodes[i + 1])?;
        let h = premises[i];
        // motive := fun (y : α) (_ : Eq α x_i y) => Eq α x0 y.
        //   Body `Eq α x0 y`: y = BVar 1; hy domain `Eq α x_i y`: y = BVar 0.
        let motive = {
            let y1 = ctx.kernel.bvar(1);
            let eq_x0_y = ctx.mk_eq(x0, y1);
            let y0 = ctx.kernel.bvar(0);
            let eq_xi_y = ctx.mk_eq(xi, y0);
            let anon = ctx.kernel.anon();
            let inner = ctx.kernel.lam(anon, eq_xi_y, eq_x0_y, BinderInfo::Default);
            ctx.kernel.lam(anon, ctx.alpha, inner, BinderInfo::Default)
        };
        // Eq.rec α x_i motive acc x_{i+1} h : Eq α x0 x_{i+1}.
        acc = ctx.mk_eq_rec_transport(xi, motive, acc, xi1, h);
    }

    let ck = ctx.alethe_term_to_expr(ck_t)?;
    let expected = ctx.mk_eq(x0, ck);
    check_against(ctx, "eq_transitive", acc, expected)
}

/// Extract `(head, args)` of an n-ary application `(head arg…)` that is **not** an
/// equality (so a genuine function application, not `(= a b)` mis-parsed).
fn as_nary_app(term: &AletheTerm) -> Option<(&str, &[AletheTerm])> {
    match term {
        AletheTerm::App(head, args) if head != "=" && !args.is_empty() => {
            Some((head.as_str(), args.as_slice()))
        }
        _ => None,
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
    /// Uninterpreted functions over a single sort (no bit-vectors).
    QfUf,
    /// Uninterpreted functions combined with bit-vectors.
    QfUfBv,
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
    /// A top-level universal quantifier.
    Forall,
    /// A top-level existential quantifier (skolemized).
    Exists,
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

/// Classify `assertions` into the [`ProofFragment`] whose emitter+reconstructor
/// pair handles it, by scanning the operators and sorts that appear. Precedence:
/// a top-level quantifier wraps any ground theory (`∃` skolemized before `∀`),
/// then the reduction theories (datatype/array), then the mixed/ground cores.
#[must_use]
pub fn scan_proof_fragment(arena: &TermArena, assertions: &[TermId]) -> ProofFragment {
    let mut has_bv = false;
    let mut has_func = false;
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
    if has_exists {
        ProofFragment::Exists
    } else if has_forall {
        ProofFragment::Forall
    } else if has_datatype {
        ProofFragment::Datatype
    } else if has_array {
        ProofFragment::QfAbv
    } else if has_func && has_bv {
        ProofFragment::QfUfBv
    } else if has_func {
        ProofFragment::QfUf
    } else if has_arith {
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
        {
            ProofFragment::Sos
        } else if crate::prove_lia_unsat_by_diophantine(arena, assertions) {
            // An integer-equality system that is integer-infeasible (`gcd ∤ const`).
            // Owned by the integer-prelude Diophantine reconstructor (ADR-0042);
            // anything else falls through to the linear Farkas (LRA) path.
            ProofFragment::Diophantine
        } else if crate::is_int_inequality_refutation(arena, assertions) {
            // A single-variable integer-INEQUALITY interval `c ≤ k·x ≤ d` (k > 0) with
            // no multiple of `k` in `[c, d]`: integer-infeasible while LP-feasible.
            // Owned by the integer-prelude inequality reconstructor (ADR-0042);
            // anything else falls through to the linear Farkas (LRA) path.
            ProofFragment::IntInequality
        } else if is_disjunctive_lra_refutation(arena, assertions) {
            // A conjunctive linear-real system plus exactly one clause `(L₁ ∨ L₂)`
            // of non-strict literals, with each leaf `conj ∧ Lᵢ` Farkas-refutable.
            // Reconstructed by a kernel case-split (`Or.rec`) reusing the per-leaf
            // conjunctive Farkas fold; the purely-conjunctive `Lra` path can never
            // match (it declines a top-level positive `Or`), so this is uncovered
            // by `reconstruct_lra_proof` today.
            ProofFragment::DisjunctiveLra
        } else {
            ProofFragment::Lra
        }
    } else if assertions.is_empty() {
        ProofFragment::Unsupported
    } else {
        ProofFragment::QfBv
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
        ProofFragment::QfAbv => {
            let p = crate::prove_qf_abv_unsat_alethe_via_elimination(arena, assertions)
                .ok_or_else(declined)?;
            let mut ctx = ReconstructCtx::new();
            let t = reconstruct_qf_ufbv_proof(&mut ctx, &p)?;
            require_infers_false(&mut ctx, t)?;
            render_ctx_module(&mut ctx, t)
        }
        ProofFragment::Datatype => {
            // Route-A is-tester fold: a pure `is_C(cⱼ x…)` contradiction is
            // discharged **by ι** (axiom-free over the fold) through the dedicated
            // tester reconstructor. Any other datatype proof (select-over-construct,
            // mixed BV residual) falls back to the general QF_UFBV reconstructor,
            // where the read-over-construct projection is itself ι-discharged.
            if let Some(module) = reconstruct_qf_dt_tester_to_lean_module(arena, assertions) {
                module?
            } else if let Some(module) =
                reconstruct_qf_dt_distinct_to_lean_module(arena, assertions)
            {
                // Constructor DISTINCTNESS `C x = D y` (C ≠ D): discharged by ι +
                // congruence + the true≠false discriminator — axiom-free, no
                // `noConfusion`. The Lean mirror of the Carcara distinctness route.
                module?
            } else {
                let p = crate::prove_qf_dt_unsat_alethe_via_simplification(arena, assertions)
                    .ok_or_else(declined)?;
                let mut ctx = ReconstructCtx::new();
                let t = reconstruct_qf_ufbv_proof(&mut ctx, &p)?;
                require_infers_false(&mut ctx, t)?;
                render_ctx_module(&mut ctx, t)
            }
        }
        ProofFragment::Forall => {
            let p = crate::prove_quant_unsat_alethe(arena, assertions).ok_or_else(declined)?;
            let mut ctx = ReconstructCtx::new();
            let t = reconstruct_quant_unsat_proof(&mut ctx, &p)?;
            require_infers_false(&mut ctx, t)?;
            render_ctx_module(&mut ctx, t)
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
        ProofFragment::Sos => {
            let mut ctx = LraReconstructCtx::new();
            let t = reconstruct_sos_proof(&mut ctx, arena, assertions)?;
            gate_and_render_lra_module(&mut ctx, t, "SOS")?
        }
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
        ProofFragment::Unsupported => {
            return Err(ReconstructError::UnsupportedRule {
                rule: "prove_unsat_to_lean: no reconstructable content".to_owned(),
            });
        }
    };
    Ok((fragment, source))
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
    if scan_proof_fragment(arena, assertions) != ProofFragment::Sos {
        return Err(ReconstructError::MalformedStep {
            rule: "reconstruct_sos_to_lean".to_owned(),
            detail: "query is not an SOS-reconstructable unsat".to_owned(),
        });
    }
    let mut ctx = LraReconstructCtx::new();
    let t = reconstruct_sos_proof(&mut ctx, arena, assertions)?;
    gate_and_render_lra_module(&mut ctx, t, "SOS")
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
                let proof = find_eq_unit(&prems, hl, hr).ok_or_else(|| {
                    ReconstructError::UnsupportedResolution {
                        detail: format!(
                            "no unit equality premise for hypothesis `(= {} {})` of `{rule}`",
                            hl.key(),
                            hr.key()
                        ),
                    }
                })?;
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

// ===========================================================================
// QF_DT **is-tester** fold — axiom-free Lean-kernel reconstruction (route A).
//
// The is-tester fold is `is_C (C x) = true` and `is_C (K x) = false` for K ≠ C
// (the SMT-LIB datatype-tester semantics). The selector route already models an
// SMT datatype constructor as a kernel inductive constructor, so the
// read-over-construct projection is ι-reduction (`Eq.refl`); this is its
// **is-tester twin**.
//
// A pure is-tester contradiction is a single redex `is_C (cⱼ x…)` asserted with
// a polarity that disagrees with the fold:
//
//   - `¬is_C (C x)` — a TRUE-fold contradiction (`is_C (C x)` ι-reduces to
//     `Bool.true`, but the assertion says it is not true); or
//   - `is_C (K x)` with `K ≠ C` — a FALSE-fold contradiction (`is_C (K x)`
//     ι-reduces to `Bool.false`, but the assertion says it is true).
//
// We model the whole datatype as ONE kernel inductive carrying every
// constructor ([`Kernel::add_datatype_family`]); the is-tester is the recursor
// application [`Kernel::datatype_tester`] eliminating into the **computational
// `Bool`**, so `is_C (cⱼ x…)` ι-reduces (kernel `whnf`/`def_eq`) to a concrete
// `Bool.true`/`Bool.false`. The is-tester predicate "`is_C(arg)` holds" is the
// Bool equality `Eq Bool (is_C arg) Bool.true`, and:
//
//   - the input assertion `is_C(arg)` / `¬is_C(arg)` is the ONLY assumed axiom
//     (the honest encoding of the input); and
//   - the fold itself is discharged BY ι — `Eq.refl Bool true` (true fold) closes
//     the negated hypothesis directly, while the false fold uses the
//     `Bool.true ≠ Bool.false` discriminator (a `Bool.rec` motive `D` with
//     `D false = True`, `D true = False`, transported along the hypothesis),
//     which is itself axiom-free (no `noConfusion` axiom, just `Bool.rec` ι).
//
// The final term `infer`s to `False` (gated by [`require_infers_false`]); a wrong
// fold makes ι fail to reduce and the kernel rejects — never a wrong `False`.
// ===========================================================================

/// A pure is-tester contradiction located in `assertions`: a tester redex
/// `is_C(cⱼ x…)` whose asserted polarity disagrees with the constructor fold.
struct TesterContradiction {
    /// The datatype of the tester's constructors.
    datatype: DatatypeId,
    /// The **tested** constructor `C` of `is_C`.
    tested: ConstructorId,
    /// The **builder** constructor `cⱼ` of the argument `cⱼ(x…)`.
    builder: ConstructorId,
    /// The builder's field argument terms (modeled as opaque carrier atoms).
    fields: Vec<TermId>,
    /// `true` when the assertion is the positive tester atom `is_C(cⱼ x…)`
    /// (a FALSE-fold contradiction needs `tested != builder`); `false` when it is
    /// the negated atom `¬is_C(cⱼ x…)` (a TRUE-fold contradiction needs
    /// `tested == builder`).
    asserted_positive: bool,
}

/// Find the first pure is-tester contradiction in `assertions`: an assertion that
/// is `is_C(cⱼ x…)` or `¬is_C(cⱼ x…)` (a tester directly over a constructor
/// application) whose polarity disagrees with the `tested == builder` fold.
/// Returns [`None`] when no such redex is present (e.g. a select-over-construct
/// proof, or a tester over a non-constructor argument).
fn find_tester_contradiction(
    arena: &TermArena,
    assertions: &[TermId],
) -> Option<TesterContradiction> {
    for &assertion in assertions {
        let (atom, positive) = match arena.node(assertion) {
            IrTermNode::App {
                op: IrOp::BoolNot,
                args,
            } => (args[0], false),
            _ => (assertion, true),
        };
        let IrTermNode::App {
            op: IrOp::DtTest(tested),
            args,
        } = arena.node(atom)
        else {
            continue;
        };
        let tested = *tested;
        let arg = args[0];
        let IrTermNode::App {
            op: IrOp::DtConstruct { constructor, .. },
            args: fields,
        } = arena.node(arg)
        else {
            continue;
        };
        let builder = *constructor;
        let folds_true = builder == tested;
        // A contradiction iff the asserted polarity disagrees with the fold:
        // positive assertion ⇒ needs the fold to be FALSE; negative ⇒ TRUE.
        if positive != folds_true {
            return Some(TesterContradiction {
                datatype: arena.constructor_datatype(tested),
                tested,
                builder,
                fields: fields.to_vec(),
                asserted_positive: positive,
            });
        }
    }
    None
}

/// **Reconstruct a pure `QF_DT` is-tester contradiction to a Lean module** whose
/// `axeyum_refutation : False` is kernel-checked and **axiom-free over the fold**
/// — the is-tester fold `is_C (C x) = true` / `is_C (K x) = false` is discharged
/// by ι-reduction (`Eq.refl`), not assumed. The only added axiom is the input
/// tester assertion itself (the honest encoding of the input constraint).
///
/// Returns [`None`] when `assertions` carry no pure is-tester contradiction
/// (the caller then falls back to the general datatype reconstructor).
///
/// # Errors
///
/// [`ReconstructError::KernelRejected`] if the datatype family fails to admit or
/// the assembled `False` term does not `infer`/`def_eq` to `False` (a defensive
/// gate; a sound fold always discharges).
fn reconstruct_qf_dt_tester_to_lean_module(
    arena: &TermArena,
    assertions: &[TermId],
) -> Option<Result<String, ReconstructError>> {
    let c = find_tester_contradiction(arena, assertions)?;
    Some(build_tester_refutation_module(arena, &c))
}

// ===========================================================================
// QF_DT **constructor DISTINCTNESS** — axiom-free Lean-kernel reconstruction
// (slice 2, the Lean mirror of the Carcara `prove_qf_dt_distinct_alethe_carcara`).
//
// An asserted constructor equality `C x… = D y…` between two **distinct**
// constructors `C ≠ D` of the *same* datatype family is UNSAT — distinct
// constructors of an inductive are never equal. We discharge it by COMPOSING
// the slice-1 is-tester primitives, with **no `noConfusion`** and **no new
// axiom** beyond the honest encoding of the input equality:
//
//   1. register the family `D` carrying every constructor
//      ([`Kernel::add_datatype_family`], reused from the tester path);
//   2. apply the is-tester for the RIGHT constructor `D`
//      ([`Kernel::datatype_tester`]): `is_D (C x…)` ι-reduces to `Bool.false`,
//      `is_D (D y…)` ι-reduces to `Bool.true`;
//   3. from the input hypothesis `h : Eq Dty (C x…) (D y…)`, transport by
//      congruence (`Eq.rec` with motive `fun z _ => Eq Bool (is_D (C x…)) (is_D z)`,
//      refl case `Eq.refl Bool (is_D (C x…))`) to `Eq Bool (is_D (C x…)) (is_D (D y…))`,
//      which is `def_eq` to `Eq Bool Bool.false Bool.true` after ι on both sides;
//   4. feed that to the EXISTING `Bool.true ≠ Bool.false` discriminator
//      ([`build_bool_true_ne_false`]): its `lhs = is_D (C x…)` ι-reduces to
//      `Bool.false`, the proof witnesses `lhs = Bool.true`, and the `Bool.rec`
//      motive `D false = True, D true = False` transported along it yields `False`.
//
// Every step is ι-reduction + `Eq.rec` — axiom-free, exactly like slice 1's
// false-fold. The final term `infer`s to `False` (gated by [`require_infers_false`]);
// a non-distinct or ill-typed equality makes ι fail and the kernel rejects —
// never a wrong `False`.
// ===========================================================================

/// A pure constructor-distinctness contradiction located in `assertions`: an
/// asserted equality `C x… = D y…` whose two constructors `C ≠ D` are **distinct**
/// constructors of the same datatype family.
struct DistinctContradiction {
    /// The shared datatype of `C` and `D`.
    datatype: DatatypeId,
    /// The left-hand-side (builder) constructor `C`.
    lhs_ctor: ConstructorId,
    /// The left-hand-side field argument terms (modeled as opaque carrier atoms).
    lhs_fields: Vec<TermId>,
    /// The right-hand-side (builder) constructor `D` — used as the tested
    /// constructor `is_D`, so the congruence yields `false = true`.
    rhs_ctor: ConstructorId,
    /// The right-hand-side field argument terms (modeled as opaque carrier atoms).
    rhs_fields: Vec<TermId>,
}

/// Find the first asserted equality `C x… = D y…` between **distinct**
/// constructors `C ≠ D` of the same datatype. Returns [`None`] when no such
/// equality is present (e.g. a same-constructor equality `C x = C y`, which is an
/// injectivity obligation handled by a separate slice, or a non-constructor
/// equality).
fn find_distinct_constructor_contradiction(
    arena: &TermArena,
    assertions: &[TermId],
) -> Option<DistinctContradiction> {
    for &assertion in assertions {
        let IrTermNode::App { op: IrOp::Eq, args } = arena.node(assertion) else {
            continue;
        };
        let &[lhs, rhs] = &args[..] else {
            continue;
        };
        let IrTermNode::App {
            op:
                IrOp::DtConstruct {
                    constructor: lhs_ctor,
                    ..
                },
            args: lhs_fields,
        } = arena.node(lhs)
        else {
            continue;
        };
        let IrTermNode::App {
            op:
                IrOp::DtConstruct {
                    constructor: rhs_ctor,
                    ..
                },
            args: rhs_fields,
        } = arena.node(rhs)
        else {
            continue;
        };
        let (lhs_ctor, rhs_ctor) = (*lhs_ctor, *rhs_ctor);
        // SAME constructor ⇒ this is an injectivity obligation, NOT distinctness;
        // decline so the distinctness reconstructor never emits a wrong `False`.
        if lhs_ctor == rhs_ctor {
            continue;
        }
        // Distinct constructors must share the same datatype (the SMT equality is
        // sort-homogeneous; guard defensively anyway).
        let datatype = arena.constructor_datatype(lhs_ctor);
        if arena.constructor_datatype(rhs_ctor) != datatype {
            continue;
        }
        return Some(DistinctContradiction {
            datatype,
            lhs_ctor,
            lhs_fields: lhs_fields.to_vec(),
            rhs_ctor,
            rhs_fields: rhs_fields.to_vec(),
        });
    }
    None
}

/// **Reconstruct a pure `QF_DT` constructor-distinctness contradiction to a Lean
/// module** whose `axeyum_refutation : False` is kernel-checked and **axiom-free
/// over the fold** — distinctness is discharged by composing the is-tester ι-fold
/// with a congruence transport and the `Bool.true ≠ Bool.false` discriminator, not
/// assumed (no `noConfusion`). The only added axiom is the input equality itself.
///
/// Returns [`None`] when `assertions` carry no distinct-constructor equality (the
/// caller then falls back to the general datatype reconstructor).
///
/// # Errors
///
/// [`ReconstructError::KernelRejected`] if the datatype family fails to admit or
/// the assembled `False` term does not `infer`/`def_eq` to `False` (a defensive
/// gate; a sound distinctness refutation always discharges).
fn reconstruct_qf_dt_distinct_to_lean_module(
    arena: &TermArena,
    assertions: &[TermId],
) -> Option<Result<String, ReconstructError>> {
    let c = find_distinct_constructor_contradiction(arena, assertions)?;
    Some(build_distinct_refutation_module(arena, &c))
}

/// Assemble the kernel `False` term for a [`DistinctContradiction`] and render the
/// Lean module. Mirrors [`build_tester_refutation_module`]: same family registry,
/// same `datatype_tester`, same `build_bool_true_ne_false` discriminator — the only
/// new piece is the `Eq.rec` congruence transport built by [`build_congr_is_d`].
fn build_distinct_refutation_module(
    arena: &TermArena,
    c: &DistinctContradiction,
) -> Result<String, ReconstructError> {
    let mut ctx = ReconstructCtx::new();

    // 1. Declare the kernel family `D` carrying EVERY constructor of the datatype
    //    (declaration order), reusing the tester path's family registry.
    let dt_name = arena.datatype_name(c.datatype).to_owned();
    let ctor_ids = arena.datatype_constructors(c.datatype).to_vec();
    let ctor_decls: Vec<(String, usize)> = ctor_ids
        .iter()
        .enumerate()
        .map(|(j, &cid)| (format!("c{j}"), arena.constructor_fields(cid).len()))
        .collect();
    let family = ctx.datatype_family(&dt_name, &ctor_decls)?;

    let lhs_pos = constructor_position(&ctor_ids, c.lhs_ctor)?;
    let rhs_pos = constructor_position(&ctor_ids, c.rhs_ctor)?;

    // 2. Build the two constructor applications `C(x…)` and `D(y…)`. Each field is a
    //    fresh opaque carrier atom (distinctness is field-independent — only the
    //    constructor head drives the is-tester ι).
    let lhs_con = build_opaque_construct(&mut ctx, family.ctors[lhs_pos], c.lhs_fields.len())?;
    let rhs_con = build_opaque_construct(&mut ctx, family.ctors[rhs_pos], c.rhs_fields.len())?;

    // 3. The is-tester for the RIGHT constructor `D`: `is_D (C x…)` ι-reduces to
    //    `Bool.false`, `is_D (D y…)` ι-reduces to `Bool.true`.
    let alpha = ctx.alpha;
    let is_d = ctx.kernel.datatype_tester(
        &family,
        ctx.prelude.bool_,
        ctx.prelude.bool_true,
        ctx.prelude.bool_false,
        alpha,
        rhs_pos,
    );
    // `is_d (C x…)` ι→ Bool.false (the discriminator `lhs`); `is_d (D y…)` ι→
    // Bool.true (the congruence's right side — built inside `build_congr_is_d`).
    let is_d_lhs = ctx.kernel.app(is_d, lhs_con);

    // 4. Input hypothesis `h : Eq Dty (C x…) (D y…)` (the ONLY added axiom). The
    //    datatype carrier in the kernel is the family inductive `Dty := D`.
    let dty = ctx.kernel.const_(family.ind, vec![]);
    let one = ctx.one;
    let eq_prop = mk_eq_at(&mut ctx, dty, one, lhs_con, rhs_con);
    let h = fresh_axiom(&mut ctx, eq_prop, "assume")?;

    // 5. Congruence transport `congrArg is_D h : Eq Bool (is_D (C x…)) (is_D (D y…))`,
    //    which is `def_eq` to `Eq Bool Bool.false Bool.true`.
    let congr = build_congr_is_d(&mut ctx, dty, is_d, lhs_con, rhs_con, h);

    // 6. The existing `Bool.true ≠ Bool.false` discriminator: `lhs = is_D (C x…)`
    //    ι-reduces to `Bool.false`, `congr : Eq Bool lhs Bool.true` ⇒ `False`.
    let false_term = build_bool_true_ne_false(&mut ctx, is_d_lhs, congr);

    require_infers_false(&mut ctx, false_term)?;
    // Render the datatype family AND the computational `Bool` as real Lean
    // `inductive`s so an external Lean regenerates their recursors *with* ι — the
    // congruence `Eq.rec` only collapses to `false = true` if Lean can compute
    // `is_D (cⱼ x…)` by ι.
    let bool_ind = ctx.prelude.bool_;
    let false_const = {
        let n = ctx.prelude().false_;
        ctx.kernel_mut().const_(n, vec![])
    };
    Ok(ctx.kernel().render_lean_module_with_inductives(
        LEAN_MODULE_THEOREM,
        false_const,
        false_term,
        &[family.ind, bool_ind],
    ))
}

/// Position of constructor `cid` in `ctor_ids` (declaration order), or a
/// [`ReconstructError::KernelRejected`] if it is not a constructor of the datatype.
fn constructor_position(
    ctor_ids: &[ConstructorId],
    cid: ConstructorId,
) -> Result<usize, ReconstructError> {
    ctor_ids
        .iter()
        .position(|&c| c == cid)
        .ok_or_else(|| ReconstructError::KernelRejected {
            rule: "datatype_distinct".to_owned(),
            detail: "constructor not in datatype".to_owned(),
        })
}

/// Build a constructor application `ctor a₀ … a_{arity-1}` whose `arity` field
/// arguments are fresh opaque carrier atoms of sort `α` (distinctness is
/// field-independent, so the exact field values are irrelevant — only the
/// constructor head drives the is-tester ι).
fn build_opaque_construct(
    ctx: &mut ReconstructCtx,
    ctor: NameId,
    arity: usize,
) -> Result<ExprId, ReconstructError> {
    let mut con = ctx.kernel.const_(ctor, vec![]);
    for i in 0..arity {
        let atom_name = ctx.fresh_name(&format!("fld_{i}"));
        let alpha = ctx.alpha;
        ctx.kernel
            .add_declaration(Declaration::Axiom {
                name: atom_name,
                uparams: vec![],
                ty: alpha,
            })
            .map_err(|e| ReconstructError::KernelRejected {
                rule: "datatype_distinct".to_owned(),
                detail: format!("field carrier atom did not admit: {e:?}"),
            })?;
        let a = ctx.kernel.const_(atom_name, vec![]);
        con = ctx.kernel.app(con, a);
    }
    Ok(con)
}

/// Build `Eq.{u} ty l r` for an arbitrary carrier type `ty : Sort u`.
fn mk_eq_at(ctx: &mut ReconstructCtx, ty: ExprId, u: LevelId, l: ExprId, r: ExprId) -> ExprId {
    let eq = ctx.kernel.const_(ctx.prelude.eq, vec![u]);
    let e = ctx.kernel.app(eq, ty);
    let e = ctx.kernel.app(e, l);
    ctx.kernel.app(e, r)
}

/// Build the congruence transport `congrArg is_D h` as an `Eq.rec`:
/// given `h : Eq dty lhs_con rhs_con` (both `dty`-typed constructor applications)
/// and the is-tester `is_d : dty → Bool`, produce a proof of
/// `Eq Bool (is_d lhs_con) (is_d rhs_con)`.
///
/// Transport motive `fun (z : dty) (_ : Eq dty lhs_con z) => Eq Bool (is_d lhs_con) (is_d z)`,
/// refl case `Eq.refl Bool (is_d lhs_con)` (the `z := lhs_con` instance is
/// `Eq Bool (is_d lhs_con) (is_d lhs_con)`), then `Eq.rec … rhs_con h` lands at
/// `Eq Bool (is_d lhs_con) (is_d rhs_con)`. Pure `Eq.rec` — axiom-free, the exact
/// `congrArg` derivation.
fn build_congr_is_d(
    ctx: &mut ReconstructCtx,
    dty: ExprId,
    is_d: ExprId,
    lhs_con: ExprId,
    rhs_con: ExprId,
    h: ExprId,
) -> ExprId {
    let anon = ctx.kernel.anon();
    let one = ctx.one;
    let bool_const = ctx.kernel.const_(ctx.prelude.bool_, vec![]);
    let is_d_lhs = ctx.kernel.app(is_d, lhs_con);

    // motive := fun (z : dty) (_ : Eq dty lhs_con z) => Eq Bool (is_d lhs_con) (is_d z).
    let transport_motive = {
        // Under binders (z : dty) (_ : Eq dty lhs_con z): `z` is bvar 1.
        let z_var = ctx.kernel.bvar(1);
        let is_d_z = ctx.kernel.app(is_d, z_var);
        let body = mk_eq_at(ctx, bool_const, one, is_d_lhs, is_d_z);
        // inner Pi binder type: Eq dty lhs_con z, with `z` as bvar 0 at this depth.
        let z0 = ctx.kernel.bvar(0);
        let eq_lhs_z = mk_eq_at(ctx, dty, one, lhs_con, z0);
        let inner = ctx.kernel.lam(anon, eq_lhs_z, body, BinderInfo::Default);
        ctx.kernel.lam(anon, dty, inner, BinderInfo::Default)
    };
    // refl_case : Eq Bool (is_d lhs_con) (is_d lhs_con) — `Eq.refl Bool (is_d lhs_con)`.
    let refl = ctx.kernel.const_(ctx.prelude.eq_refl, vec![ctx.one]);
    let refl_case = {
        let e = ctx.kernel.app(refl, bool_const);
        ctx.kernel.app(e, is_d_lhs)
    };
    // Eq.rec.{v,u} dty lhs_con transport_motive refl_case rhs_con h
    //   : Eq Bool (is_d lhs_con) (is_d rhs_con).
    // motive `fun z _ => Eq Bool …` eliminates into `Prop` ⇒ v = 0; the equands of
    // `h` are `dty : Sort 1` ⇒ u = 1 (= `ctx.one`).
    let v = ctx.kernel.level_zero();
    let rec_eq = ctx.kernel.const_(ctx.prelude.eq_rec, vec![v, one]);
    let e = ctx.kernel.app(rec_eq, dty);
    let e = ctx.kernel.app(e, lhs_con);
    let e = ctx.kernel.app(e, transport_motive);
    let e = ctx.kernel.app(e, refl_case);
    let e = ctx.kernel.app(e, rhs_con);
    ctx.kernel.app(e, h)
}

/// Assemble the kernel `False` term for a [`TesterContradiction`] and render the
/// Lean module. Split out so the entry point stays a thin Option wrapper.
fn build_tester_refutation_module(
    arena: &TermArena,
    c: &TesterContradiction,
) -> Result<String, ReconstructError> {
    let mut ctx = ReconstructCtx::new();

    // 1. Declare the kernel family `D` carrying EVERY constructor of the datatype
    //    (in declaration order), so the recursor can distinguish them.
    let dt_name = arena.datatype_name(c.datatype).to_owned();
    let ctor_ids = arena.datatype_constructors(c.datatype).to_vec();
    // Constructor LEAF names `c0, c1, …` (kept positional + Lean-identifier-safe;
    // `datatype_family` namespaces them under the family inductive so Lean's
    // regenerated constructor/recursor names match).
    let ctor_decls: Vec<(String, usize)> = ctor_ids
        .iter()
        .enumerate()
        .map(|(j, &cid)| (format!("c{j}"), arena.constructor_fields(cid).len()))
        .collect();
    let family = ctx.datatype_family(&dt_name, &ctor_decls)?;

    // 2. Build the constructor application `cⱼ(x…)`: model each field as a fresh
    //    opaque carrier atom `α` (the fold is field-independent, so the exact
    //    field value is irrelevant — only the constructor head drives ι).
    let builder_pos = ctor_ids
        .iter()
        .position(|&cid| cid == c.builder)
        .ok_or_else(|| ReconstructError::KernelRejected {
            rule: "datatype_tester".to_owned(),
            detail: "builder constructor not in datatype".to_owned(),
        })?;
    let tested_pos = ctor_ids
        .iter()
        .position(|&cid| cid == c.tested)
        .ok_or_else(|| ReconstructError::KernelRejected {
            rule: "datatype_tester".to_owned(),
            detail: "tested constructor not in datatype".to_owned(),
        })?;
    let mut con = ctx.kernel.const_(family.ctors[builder_pos], vec![]);
    for (i, _field) in c.fields.iter().enumerate() {
        let atom_name = ctx.fresh_name(&format!("fld_{i}"));
        let alpha = ctx.alpha;
        ctx.kernel
            .add_declaration(Declaration::Axiom {
                name: atom_name,
                uparams: vec![],
                ty: alpha,
            })
            .map_err(|e| ReconstructError::KernelRejected {
                rule: "datatype_tester".to_owned(),
                detail: format!("field carrier atom did not admit: {e:?}"),
            })?;
        let a = ctx.kernel.const_(atom_name, vec![]);
        con = ctx.kernel.app(con, a);
    }

    // 3. The is-tester `is_C : D → Bool` and the fold `is_C(cⱼ x…)`.
    let alpha = ctx.alpha;
    let tester = ctx.kernel.datatype_tester(
        &family,
        ctx.prelude.bool_,
        ctx.prelude.bool_true,
        ctx.prelude.bool_false,
        alpha,
        tested_pos,
    );
    let folded = ctx.kernel.app(tester, con);
    let bool_true = ctx.kernel.const_(ctx.prelude.bool_true, vec![]);

    // The is-tester predicate atom "is_C(arg) holds" := Eq Bool (is_C arg) true.
    let pred = ctx.mk_eq_bool(folded, bool_true);

    let false_term = if c.asserted_positive {
        // FALSE fold: assertion `is_C(K x)` ⇒ axiom `h : Eq Bool (is_C(K x)) true`.
        // But `is_C(K x)` ι-reduces to `Bool.false`, so `h` proves `false = true`
        // (def_eq). The `Bool.true ≠ Bool.false` discriminator yields `False`.
        let h = fresh_axiom(&mut ctx, pred, "assume")?;
        build_bool_true_ne_false(&mut ctx, folded, h)
    } else {
        // TRUE fold: assertion `¬is_C(C x)` ⇒ axiom `h : ¬(Eq Bool (is_C(C x)) true)`.
        // `is_C(C x)` ι-reduces to `Bool.true`, so `Eq.refl Bool true` proves the
        // predicate; applying `h` to it gives `False`.
        let not_pred = ctx.mk_not(pred);
        let h = fresh_axiom(&mut ctx, not_pred, "assume")?;
        let refl = ctx.mk_eq_refl_bool(bool_true);
        ctx.kernel.app(h, refl)
    };

    require_infers_false(&mut ctx, false_term)?;
    // Render the datatype family AND the computational `Bool` as **real Lean
    // `inductive`s** so an external Lean regenerates their recursors *with* ι — the
    // is-tester fold `Eq.refl Bool (true/false)` only type-checks if Lean can
    // compute `is_C (cⱼ x…)` by ι. Everything else (the logical prelude, the input
    // hypothesis axiom) renders as before.
    let bool_ind = ctx.prelude.bool_;
    let false_const = {
        let n = ctx.prelude().false_;
        ctx.kernel_mut().const_(n, vec![])
    };
    Ok(ctx.kernel().render_lean_module_with_inductives(
        LEAN_MODULE_THEOREM,
        false_const,
        false_term,
        &[family.ind, bool_ind],
    ))
}

/// Given `lhs` (a `Bool` term that ι-reduces to `Bool.false`) and a proof
/// `h : Eq Bool lhs Bool.true`, build a proof of `False` using the
/// `Bool.true ≠ Bool.false` discriminator — **axiom-free**, by `Bool.rec` ι.
///
/// The discriminator motive is `D := λ (b : Bool), Bool.rec (λ _ => Prop) False
/// True b`, so `D Bool.false` ι-reduces to `True` and `D Bool.true` to `False`.
/// Transporting `True.intro : D lhs` (`lhs` `def_eq` `Bool.false`, so `D lhs`
/// `def_eq` `True`) along `h` to `D Bool.true` (`def_eq` `False`) is the refutation.
fn build_bool_true_ne_false(ctx: &mut ReconstructCtx, lhs: ExprId, h: ExprId) -> ExprId {
    let anon = ctx.kernel.anon();
    let bool_const = ctx.kernel.const_(ctx.prelude.bool_, vec![]);
    let prop = ctx.kernel.sort_zero();
    let true_const = ctx.kernel.const_(ctx.prelude.true_, vec![]);
    let false_const = ctx.kernel.const_(ctx.prelude.false_, vec![]);

    // discr := λ (b : Bool), Bool.rec.{1} (motive := λ _ => Prop) False True b.
    //   minor for Bool.true  = False ;  minor for Bool.false = True.
    // The motive `λ _ => Prop` maps `Bool → Sort 1` (since `Prop : Sort 1`), so the
    // (large) elimination universe is `1`.
    let z = ctx.kernel.level_zero();
    let one = ctx.kernel.level_succ(z);
    let rec = ctx.kernel.const_(ctx.prelude.bool_rec, vec![one]);
    let motive = ctx.kernel.lam(anon, bool_const, prop, BinderInfo::Default);
    let discr = {
        let e = ctx.kernel.app(rec, motive);
        let e = ctx.kernel.app(e, false_const); // minor for Bool.true
        let e = ctx.kernel.app(e, true_const); // minor for Bool.false
        let b = ctx.kernel.bvar(0);
        let body = ctx.kernel.app(e, b);
        ctx.kernel.lam(anon, bool_const, body, BinderInfo::Default)
    };

    // The Eq.rec transport motive `fun (x : Bool) (_ : Eq Bool lhs x) => discr x`.
    // `discr lhs` def_eq `True`, so the refl case is `True.intro : discr lhs`.
    let bool_true = ctx.kernel.const_(ctx.prelude.bool_true, vec![]);
    let transport_motive = {
        // Under binders (x : Bool) (_ : Eq Bool lhs x): apply `discr` to `x`(=bvar 1).
        let x = ctx.kernel.bvar(1);
        let discr_x = ctx.kernel.app(discr, x);
        // inner Pi binder type: Eq Bool lhs x. `lhs` is closed (no bound vars here),
        // `x` is bvar 0 at this binder depth.
        let eq = ctx.kernel.const_(ctx.prelude.eq, vec![ctx.one]);
        let x0 = ctx.kernel.bvar(0);
        let eq_lhs_x = {
            let e = ctx.kernel.app(eq, bool_const);
            let e = ctx.kernel.app(e, lhs);
            ctx.kernel.app(e, x0)
        };
        let inner = ctx.kernel.lam(anon, eq_lhs_x, discr_x, BinderInfo::Default);
        ctx.kernel.lam(anon, bool_const, inner, BinderInfo::Default)
    };
    // refl_case : discr lhs  (def_eq True) — `True.intro`.
    let refl_case = ctx.kernel.const_(ctx.prelude.true_intro, vec![]);
    // Eq.rec.{0,1} Bool lhs transport_motive refl_case Bool.true h : discr Bool.true
    //   = False (def_eq).
    let rec_eq = ctx.kernel.const_(ctx.prelude.eq_rec, vec![z, ctx.one]);
    let e = ctx.kernel.app(rec_eq, bool_const);
    let e = ctx.kernel.app(e, lhs);
    let e = ctx.kernel.app(e, transport_motive);
    let e = ctx.kernel.app(e, refl_case);
    let e = ctx.kernel.app(e, bool_true);
    ctx.kernel.app(e, h)
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

// ===========================================================================
// Quantifier instantiation (the first quantified-`unsat` slice) — reconstruct
// a `forall_inst`-driven refutation to a kernel-checked `False`.
//
// ## Kernel modeling of ∀
//
// A universal `∀(x : α). P(x)` over the EUF carrier `α` is the **dependent
// product** `Pi (x : α), ⟦P x⟧`, where `⟦P x⟧ : Prop` is the body's translation
// with the bound variable rendered as the de-Bruijn `bvar(0)` (this slice's
// bodies are quantifier-free, so `x` is always at index 0). The universal
// hypothesis is declared as an axiom `h_forall : Pi (x : α), ⟦P x⟧`.
//
// **Instantiation is application** (`forall_elim`): for a witness `t`,
// `h_forall ⟦t⟧ : ⟦P x⟧[bvar 0 := ⟦t⟧]`, and the kernel's `infer` β/Pi-reduces
// that to `⟦P t⟧` — exactly the ground instance equality. The reconstructed
// instance is therefore an ordinary [`ClauseProof::EqUnit`] whose proof term is
// the application, and the **ground tail** (the EUF resolution to the empty
// clause) is the existing [`reconstruct_qf_uf_proof`] machinery threaded with
// these instance units.
//
// ## Soundness
//
// Every instance application is `infer`/`def_eq`-checked against the translated
// instance equality before it enters the ground walk, and the final `False` goes
// through [`check_false`] — so a wrong witness, a wrong Pi body, or a mis-shaped
// `forall_inst` makes the kernel reject it (a `ReconstructError`), never a wrong
// `False`. The only addition to the trusted base is one axiom per quantified
// assertion — the honest encoding of the input universal.
// ===========================================================================

impl ReconstructCtx {
    /// Translate an Alethe term into a Lean [`ExprId`] in the EUF model, with each
    /// quantified variable in `var_names` rendered as a de-Bruijn `bvar`. The list
    /// is outermost-first, matching the binder chain `Pi (x₀:α), … Pi (xₙ:α), …`;
    /// variable `var_names[i]` therefore sits at de-Bruijn index
    /// `var_names.len() - 1 - i` (the **innermost** binder is index 0). For a single
    /// universal (`var_names = [x]`) this is `bvar(0)`, as before.
    ///
    /// # Errors
    ///
    /// As [`Self::alethe_term_to_expr`]: [`ReconstructError::UnsupportedTerm`] for
    /// an out-of-scope shape.
    fn alethe_term_to_expr_bound(
        &mut self,
        term: &AletheTerm,
        var_names: &[&str],
    ) -> Result<ExprId, ReconstructError> {
        match term {
            AletheTerm::Const(symbol) => {
                if let Some(i) = var_names.iter().position(|v| v == symbol) {
                    // de-Bruijn index: innermost binder (last in `var_names`) is 0.
                    let index = u32::try_from(var_names.len() - 1 - i)
                        .map_err(|_| ReconstructError::UnsupportedTerm { term: term.key() })?;
                    Ok(self.kernel.bvar(index))
                } else {
                    let name = self.atom_const(symbol);
                    Ok(self.kernel.const_(name, vec![]))
                }
            }
            AletheTerm::App(head, args) if head == "=" => {
                let [l, r] = args.as_slice() else {
                    return Err(ReconstructError::UnsupportedTerm { term: term.key() });
                };
                let l = self.alethe_term_to_expr_bound(l, var_names)?;
                let r = self.alethe_term_to_expr_bound(r, var_names)?;
                Ok(self.mk_eq(l, r))
            }
            AletheTerm::App(head, args) if !args.is_empty() => {
                let f_name = self.func_const(head, args.len());
                let mut e = self.kernel.const_(f_name, vec![]);
                for arg in args {
                    let a = self.alethe_term_to_expr_bound(arg, var_names)?;
                    e = self.kernel.app(e, a);
                }
                Ok(e)
            }
            AletheTerm::App(..) | AletheTerm::Indexed { .. } => {
                Err(ReconstructError::UnsupportedTerm { term: term.key() })
            }
        }
    }
}

/// What a parsed (possibly nested) Alethe `(forall (x) … body)` atom carries: the
/// ordered bound-variable names (outermost first) and the quantifier-free inner
/// body, ready for translation.
struct ForallAtom<'a> {
    var_names: Vec<&'a str>,
    body: &'a AletheTerm,
}

/// Parse a (possibly nested) `(forall (x) (forall (y) … body))` Alethe atom — the
/// opaque universal the quantifier emitter `assume`s. Each level is encoded as
/// `App("forall", [Const(x), inner])`; this peels the chain, collecting the bound
/// variables outermost-first and returning the innermost quantifier-free body.
/// `None` if `atom` is not a `forall` chain.
fn as_forall_atom(atom: &AletheTerm) -> Option<ForallAtom<'_>> {
    let mut var_names = Vec::new();
    let mut cur = atom;
    while let AletheTerm::App(head, args) = cur {
        if head != "forall" || args.len() != 2 {
            break;
        }
        let AletheTerm::Const(var_name) = &args[0] else {
            return None;
        };
        var_names.push(var_name.as_str());
        cur = &args[1];
    }
    if var_names.is_empty() {
        return None;
    }
    Some(ForallAtom {
        var_names,
        body: cur,
    })
}

/// Infer the witness **tuple** `[t₀, …]` (one per bound variable in `var_names`,
/// in that order) by matching the instance `inst` against `body[xᵢ := ?]`: the
/// first occurrence of each `Const(xᵢ)` fixes `tᵢ`, later occurrences must agree,
/// and all other structure must match verbatim. Returns the witnesses, or `None`
/// if `inst` is not a consistent instance of `body` (so a malformed `forall_inst`
/// is rejected rather than mis-reconstructed), or if any bound variable does not
/// occur in `body` (no witness to apply) — out of this slice.
fn infer_witness<'a>(
    var_names: &[&str],
    body: &AletheTerm,
    inst: &'a AletheTerm,
) -> Option<Vec<&'a AletheTerm>> {
    fn go<'a>(
        var_names: &[&str],
        body: &AletheTerm,
        inst: &'a AletheTerm,
        witnesses: &mut BTreeMap<String, &'a AletheTerm>,
    ) -> bool {
        match body {
            AletheTerm::Const(c) if var_names.iter().any(|v| v == c) => {
                if let Some(w) = witnesses.get(c) {
                    *w == inst
                } else {
                    witnesses.insert(c.clone(), inst);
                    true
                }
            }
            AletheTerm::Const(_) => body == inst,
            AletheTerm::App(bh, ba) => {
                let AletheTerm::App(ih, ia) = inst else {
                    return false;
                };
                bh == ih
                    && ba.len() == ia.len()
                    && ba
                        .iter()
                        .zip(ia)
                        .all(|(b, i)| go(var_names, b, i, witnesses))
            }
            AletheTerm::Indexed {
                op: bo,
                indices: bi,
                args: ba,
            } => {
                let AletheTerm::Indexed {
                    op: io,
                    indices: ii,
                    args: ia,
                } = inst
                else {
                    return false;
                };
                bo == io
                    && bi == ii
                    && ba.len() == ia.len()
                    && ba
                        .iter()
                        .zip(ia)
                        .all(|(b, i)| go(var_names, b, i, witnesses))
            }
        }
    }
    let mut witnesses: BTreeMap<String, &'a AletheTerm> = BTreeMap::new();
    if !go(var_names, body, inst, &mut witnesses) {
        return None;
    }
    // Every bound variable must have been bound (occur in the body).
    var_names
        .iter()
        .map(|v| witnesses.get(*v).copied())
        .collect()
}

/// A `forall_inst` clause `(cl (not (forall (x) … body)) inst)` recorded for lazy
/// reconstruction: it is turned into a ground-instance unit when a `resolution`
/// resolves it against the universal axiom.
#[derive(Clone)]
struct ForallInstClause {
    /// The bound variable names of the universal it instantiates (outermost first).
    var_names: Vec<String>,
    /// The universal inner body (with the bound variables free, as `Const(x)`).
    body: AletheTerm,
    /// The instance literal `inst = body[xᵢ := tᵢ]` (positive).
    inst: AletheTerm,
}

/// The reconstruction environment for the quantifier walk: a per-id map to either
/// a ground [`ClauseProof`] (reusing the EUF machinery), a universal axiom, or a
/// pending `forall_inst` clause.
enum QuantProof {
    /// A ground clause proof (unit equality/disequality or EUF theory clause),
    /// reconstructed exactly as the EUF walk does.
    Ground(ClauseProof),
    /// A universal `assume`: the dependent-product axiom
    /// `h : Pi (x:α), … Pi (xₙ:α), ⟦body⟧`, with its binder names and body kept for
    /// witness translation.
    ForallAxiom {
        /// The bound variable names (outermost first).
        var_names: Vec<String>,
        /// The universal inner body (Alethe, the bound variables free).
        body: AletheTerm,
        /// The axiom proof term `h_forall : Pi (x:α), … ⟦body⟧`.
        proof: ExprId,
    },
    /// A pending `forall_inst` theory clause, reconstructed on resolution.
    Inst(ForallInstClause),
}

/// Reconstruct a **complete** quantifier-instantiation `unsat` Alethe proof (the
/// shape [`crate::prove_quant_unsat_alethe`] emits) into a Lean proof term of type
/// `False` that the trusted [`Kernel`] type-checks.
///
/// The proof's quantifier layer is an `assume` of the universal over an opaque
/// `(forall (x) body)` atom, one `forall_inst` step per witness, and a
/// `resolution` of each `forall_inst` against the universal to the ground instance
/// unit; the ground tail is the EUF refutation of those instances plus the side
/// assertions (the `prove_qf_uf_unsat_alethe` shape, here with ids prefixed `g_`).
///
/// ## How each command maps
///
/// - **`assume (cl (forall (x) body))`** ⇒ an axiom `h : Pi (x:α), ⟦body⟧` (the
///   universal as a dependent product; `forall_elim` is its application).
/// - **`assume (cl …)`** (an equality / disequality side fact) ⇒ the EUF
///   `reconstruct_assume` unit hypothesis.
/// - **`forall_inst (cl (not (forall (x) body)) inst)`** ⇒ recorded pending.
/// - **`resolution [forall-axiom, forall_inst]`** ⇒ `h ⟦t⟧ : ⟦inst⟧` (the witness
///   `t` inferred from `inst = body[x:=t]`), an `infer`-checked ground unit.
/// - **`eq_*`/`resolution`/`th_resolution`/empty clause** ⇒ the EUF
///   `reconstruct_resolution` machinery, closing to `False`.
///
/// # Errors
///
/// Returns a [`ReconstructError`] for any out-of-scope command shape, an unknown
/// premise id, a malformed `forall_inst`/resolution, a missing empty-clause
/// derivation, or a kernel rejection. It never panics on malformed input.
pub fn reconstruct_quant_unsat_proof(
    ctx: &mut ReconstructCtx,
    commands: &[AletheCommand],
) -> Result<ExprId, ReconstructError> {
    let mut env: BTreeMap<String, QuantProof> = BTreeMap::new();

    for cmd in commands {
        match cmd {
            AletheCommand::Assume { id, clause } => {
                // A universal `(cl (forall (x) body))`, or an ordinary EUF unit.
                if let [l] = clause.as_slice() {
                    if !l.negated {
                        if let Some(fa) = as_forall_atom(&l.atom) {
                            let var_names: Vec<String> =
                                fa.var_names.iter().map(|&s| s.to_owned()).collect();
                            let body = fa.body.clone();
                            let proof = declare_forall_axiom(ctx, &fa.var_names, &body)?;
                            env.insert(
                                id.clone(),
                                QuantProof::ForallAxiom {
                                    var_names,
                                    body,
                                    proof,
                                },
                            );
                            continue;
                        }
                    }
                }
                let cp = reconstruct_assume(ctx, clause)?;
                env.insert(id.clone(), QuantProof::Ground(cp));
            }
            AletheCommand::Step {
                id,
                clause,
                rule,
                premises,
                ..
            } => match rule.as_str() {
                "forall_inst" => {
                    let inst_clause = parse_forall_inst(clause)?;
                    env.insert(id.clone(), QuantProof::Inst(inst_clause));
                }
                "eq_reflexive" | "eq_symmetric" | "eq_transitive" | "eq_congruent" => {
                    env.insert(
                        id.clone(),
                        QuantProof::Ground(ClauseProof::TheoryClause {
                            rule: rule.clone(),
                            clause: clause.clone(),
                        }),
                    );
                }
                "resolution" | "th_resolution" => {
                    // A quantifier resolution (forall-axiom against a forall_inst)
                    // yields the ground instance unit; otherwise it is a ground EUF
                    // resolution / the closing empty clause.
                    if let Some(unit) = try_instance_resolution(ctx, premises, &env)? {
                        env.insert(id.clone(), QuantProof::Ground(unit));
                        continue;
                    }
                    let ground_env = ground_view(&env);
                    match reconstruct_resolution(ctx, clause, premises, &ground_env)? {
                        ResolutionResult::Clause(cp) => {
                            env.insert(id.clone(), QuantProof::Ground(cp));
                        }
                        ResolutionResult::FalseProof(proof) => {
                            return check_false(ctx, proof);
                        }
                    }
                }
                other => {
                    return Err(ReconstructError::UnsupportedRule {
                        rule: other.to_owned(),
                    });
                }
            },
        }
    }

    Err(ReconstructError::NoEmptyClause)
}

/// Declare the universal axiom `h : Pi (x : α), … Pi (xₙ : α), ⟦body⟧` (one binder
/// per name in `var_names`, outermost first) and return its `Const`.
fn declare_forall_axiom(
    ctx: &mut ReconstructCtx,
    var_names: &[&str],
    body: &AletheTerm,
) -> Result<ExprId, ReconstructError> {
    let mut ty = ctx.alethe_term_to_expr_bound(body, var_names)?;
    let anon = ctx.kernel.anon();
    // Wrap one `Pi (· : α)` per bound variable. Each wrap adds an outer binder, so
    // the count is what matters; `alethe_term_to_expr_bound` already placed each
    // variable at its de-Bruijn index for this nesting depth.
    for _ in var_names {
        ty = ctx.kernel.pi(anon, ctx.alpha, ty, BinderInfo::Default);
    }
    fresh_axiom(ctx, ty, "forall")
}

/// Parse a `forall_inst` step's clause `(cl (not (forall (x) … body)) inst)`.
fn parse_forall_inst(clause: &[AletheLit]) -> Result<ForallInstClause, ReconstructError> {
    let [neg, pos] = clause else {
        return Err(ReconstructError::MalformedStep {
            rule: "forall_inst".to_owned(),
            detail: "expected exactly two literals `(not (forall …)) inst`".to_owned(),
        });
    };
    if !neg.negated || pos.negated {
        return Err(ReconstructError::MalformedStep {
            rule: "forall_inst".to_owned(),
            detail: "literal polarities are not `(not (forall …))` then positive `inst`".to_owned(),
        });
    }
    let Some(fa) = as_forall_atom(&neg.atom) else {
        return Err(ReconstructError::MalformedStep {
            rule: "forall_inst".to_owned(),
            detail: "first literal is not a `(forall (x) … body)` atom".to_owned(),
        });
    };
    Ok(ForallInstClause {
        var_names: fa.var_names.iter().map(|&s| s.to_owned()).collect(),
        body: fa.body.clone(),
        inst: pos.atom.clone(),
    })
}

/// If `premises` are exactly a universal axiom and a pending `forall_inst` over the
/// same universal, reconstruct the instance unit `(h ⟦t₀⟧ …) : ⟦inst⟧`
/// (`forall_elim`, one application per bound variable). Returns `Ok(Some(unit))` on
/// a quantifier resolution, `Ok(None)` when it is not one (so the caller falls back
/// to the EUF resolution path).
fn try_instance_resolution(
    ctx: &mut ReconstructCtx,
    premises: &[String],
    env: &BTreeMap<String, QuantProof>,
) -> Result<Option<ClauseProof>, ReconstructError> {
    // Find an axiom premise and an inst premise (order-independent).
    let mut axiom: Option<(&[String], &AletheTerm, ExprId)> = None;
    let mut inst: Option<&ForallInstClause> = None;
    for p in premises {
        match env.get(p) {
            Some(QuantProof::ForallAxiom {
                var_names,
                body,
                proof,
            }) => axiom = Some((var_names, body, *proof)),
            Some(QuantProof::Inst(ic)) => inst = Some(ic),
            _ => {}
        }
    }
    let (Some((ax_vars, ax_body, ax_proof)), Some(ic)) = (axiom, inst) else {
        return Ok(None);
    };
    // The inst clause must instantiate this very universal.
    if ic.var_names != ax_vars || &ic.body != ax_body {
        return Err(ReconstructError::UnsupportedResolution {
            detail: "forall_inst resolves against a different universal".to_owned(),
        });
    }
    // Infer the witness tuple from `inst = body[xᵢ := tᵢ]`, translate each, and
    // apply the axiom to them in binder order (outermost first).
    let ax_var_refs: Vec<&str> = ax_vars.iter().map(String::as_str).collect();
    let witnesses = infer_witness(&ax_var_refs, ax_body, &ic.inst).ok_or_else(|| {
        ReconstructError::MalformedStep {
            rule: "forall_inst".to_owned(),
            detail: "instance is not a consistent substitution of the universal body".to_owned(),
        }
    })?;
    // forall_elim chain: (((h ⟦t₀⟧) ⟦t₁⟧) …) : ⟦body⟧[xᵢ := ⟦tᵢ⟧]  (≡ ⟦inst⟧).
    let mut app = ax_proof;
    for witness in witnesses {
        let t_expr = ctx.alethe_term_to_expr(witness)?;
        app = ctx.kernel.app(app, t_expr);
    }
    // Validate against the translated instance and package as the matching unit.
    if let Some((l, r)) = as_positive_eq(&AletheLit {
        atom: ic.inst.clone(),
        negated: false,
    }) {
        let le = ctx.alethe_term_to_expr(l)?;
        let re = ctx.alethe_term_to_expr(r)?;
        let expected = ctx.mk_eq(le, re);
        let proof = check_against(ctx, "forall_inst", app, expected)?;
        Ok(Some(ClauseProof::EqUnit {
            l: l.clone(),
            r: r.clone(),
            proof,
        }))
    } else {
        Err(ReconstructError::UnsupportedResolution {
            detail: "forall_inst instance is not an equality (outside this EUF slice)".to_owned(),
        })
    }
}

/// A read-only [`ClauseProof`] view of the quantifier environment for the EUF
/// resolution machinery: ground entries pass through; an axiom / pending inst is
/// not a ground clause and is omitted (a resolution citing one as a ground premise
/// is a real shape error the EUF path will surface).
fn ground_view(env: &BTreeMap<String, QuantProof>) -> BTreeMap<String, ClauseProof> {
    let mut out = BTreeMap::new();
    for (id, qp) in env {
        if let QuantProof::Ground(cp) = qp {
            out.insert(id.clone(), cp.clone());
        }
    }
    out
}

// ===========================================================================
// Existential skolemization (P3.7) — CERTIFY the trusted skolemization step.
//
// ## The certificate and what it certifies
//
// [`crate::solve`] replaces a top-level `∃x. P(x)` with `P(sk)` for a fresh
// constant `sk` and refutes the skolemized query — a *trusted* step. The
// emitter [`crate::prove_skolem_unsat_alethe`] produces a [`crate::SkolemCert`]: an
// Alethe proof of the **skolemized** refutation (where each `sk_k` is an
// ordinary uninterpreted constant and each `P(sk_k)` is an `assume`d EUF unit)
// plus, per existential, the bound-variable name, the single-equality body `P`
// (bound variable free), and the skolem name `sk_k`.
//
// ## Kernel modeling of ∃ and the `Exists.elim` wrapping
//
// `∃(x : α). P(x)` is the prelude inductive `Exists.{1} α p` with
// `p := fun (x : α) => ⟦P x⟧ : α → Prop`. The existential hypothesis is the
// honest axiom `h_∃ : Exists α p` (mirroring how a universal becomes a `Pi`
// axiom).
//
// The skolemized refutation `R : False` is reconstructed by the existing
// quantifier walk; it mentions `Const(sk_k)` (the skolem atom) and
// `Const(hyp_k)` (the `P(sk_k)` assumption axiom). `R` is **parametric** in
// these: it refutes `P(sk_k) ∧ Rest` for the *arbitrary* constant `sk_k`. So,
// replacing each `Const(sk_k) ↦ w_k` and `Const(hyp_k) ↦ hw_k` turns `R` into
// the minor premise `fun (w_k : α) (hw_k : p_k w_k) => R'` and
//
//     Exists.rec.{0,1} α p_k (fun _ => False) (fun w_k hw_k => R') h_∃_k : False
//
// is the `Exists.elim`. Several existentials nest (innermost-out). The skolem
// atom and assumption are turned into fresh **fvars** first, then the standard
// `abstract_fvars` + `lam` machinery handles binder depth.
//
// ## Soundness
//
// The minor's body is the same kernel-checked refutation `R`; the
// `Exists.rec` applications and the final term are `infer`/`def_eq False`-gated
// through [`check_false`]. The only additions to the trusted base are the per-`∃`
// axiom `h_∃_k` (the honest encoding of the input existential) and whatever the
// inner refutation already adds (the universal axioms / side `assume`s). A wrong
// body `p_k`, a mis-identified skolem/assumption, or a wrong nesting makes the
// kernel reject the `Exists.rec` application — never a wrong `False`.
// ===========================================================================

impl ReconstructCtx {
    /// The constant [`NameId`] previously declared (lazily) for the EUF atom
    /// `name`, if any. Used by the skolem reconstruction to locate a skolem
    /// constant after the inner refutation has been reconstructed.
    fn atom_name_id(&self, name: &str) -> Option<NameId> {
        self.atoms.get(name).copied()
    }

    /// Replace every `Const(target, _)` in `e` with the expression `repl`,
    /// **correctly shifting** `repl` under intervening binders. Here `repl` is
    /// always a loose `BVar` (the `Exists.elim`-bound variable), so passing
    /// through a binder lifts it by one. A pure structural rewrite over the public
    /// expression constructors — no reduction.
    fn replace_const(&mut self, e: ExprId, target: NameId, repl: ExprId) -> ExprId {
        self.replace_const_aux(e, target, repl, 0)
    }

    fn replace_const_aux(&mut self, e: ExprId, target: NameId, repl: ExprId, depth: u32) -> ExprId {
        match self.kernel.expr_node(e).clone() {
            ExprNode::Const(n, _) if n == target => {
                // Lift the (loose-bvar) replacement to the current binder depth.
                self.kernel.lift_loose_bvars(repl, 0, depth)
            }
            ExprNode::BVar(_)
            | ExprNode::FVar(_)
            | ExprNode::Sort(_)
            | ExprNode::Const(..)
            | ExprNode::Lit(_) => e,
            ExprNode::App(f, a) => {
                let f = self.replace_const_aux(f, target, repl, depth);
                let a = self.replace_const_aux(a, target, repl, depth);
                self.kernel.app(f, a)
            }
            ExprNode::Lam(name, ty, body, info) => {
                let ty = self.replace_const_aux(ty, target, repl, depth);
                let body = self.replace_const_aux(body, target, repl, depth + 1);
                self.kernel.lam(name, ty, body, info)
            }
            ExprNode::Pi(name, ty, body, info) => {
                let ty = self.replace_const_aux(ty, target, repl, depth);
                let body = self.replace_const_aux(body, target, repl, depth + 1);
                self.kernel.pi(name, ty, body, info)
            }
            ExprNode::Let(name, ty, val, body) => {
                let ty = self.replace_const_aux(ty, target, repl, depth);
                let val = self.replace_const_aux(val, target, repl, depth);
                let body = self.replace_const_aux(body, target, repl, depth + 1);
                self.kernel.let_(name, ty, val, body)
            }
        }
    }

    /// Build the existential predicate `p := fun (x : α) => ⟦body x⟧ : α → Prop`
    /// and the proposition `Exists.{1} α p`, from a single-equality `body` whose
    /// bound variable is `bound_var`.
    fn mk_exists(
        &mut self,
        bound_var: &str,
        body: &AletheTerm,
    ) -> Result<(ExprId, ExprId), ReconstructError> {
        // ⟦body⟧ with the bound variable at de-Bruijn 0 (a one-binder context).
        let body_expr = self.alethe_term_to_expr_bound(body, &[bound_var])?;
        let anon = self.kernel.anon();
        // p := fun (x : α) => ⟦body⟧.
        let p = self
            .kernel
            .lam(anon, self.alpha, body_expr, BinderInfo::Default);
        // Exists.{1} α p.
        let exists_const = self.kernel.const_(self.prelude.exists_, vec![self.one]);
        let e = self.kernel.app(exists_const, self.alpha);
        let exists_ap = self.kernel.app(e, p);
        Ok((p, exists_ap))
    }

    /// `Exists.rec.{0,1} α p (fun _ => False) minor major : False` — the
    /// `Exists.elim` at a constant `False` motive.
    fn mk_exists_elim_false(
        &mut self,
        p: ExprId,
        exists_ap: ExprId,
        minor: ExprId,
        major: ExprId,
    ) -> ExprId {
        let z = self.kernel.level_zero();
        let anon = self.kernel.anon();
        let false_ = self.kernel.const_(self.prelude.false_, vec![]);
        // motive := fun (_ : Exists α p) => False.
        let motive = self
            .kernel
            .lam(anon, exists_ap, false_, BinderInfo::Default);
        let rec = self
            .kernel
            .const_(self.prelude.exists_rec, vec![z, self.one]);
        let e = self.kernel.app(rec, self.alpha);
        let e = self.kernel.app(e, p);
        let e = self.kernel.app(e, motive);
        let e = self.kernel.app(e, minor);
        self.kernel.app(e, major)
    }
}

/// One skolemized existential prepared for the `Exists.elim` wrapping: the
/// predicate `p_k`, the proposition `Exists α p_k`, the existential hypothesis
/// axiom `h_∃_k`, and the skolem-constant / `P(sk_k)`-assumption `NameId`s.
///
/// The `NameId`s are `Option`: when the skolemized refutation does **not** use
/// the witness (the inner refutation closes from the side facts alone — possible
/// only when the existential was *vacuous* to the contradiction), the skolem
/// atom and/or its assumption are never interned/declared by the inner walk, and
/// the corresponding `Exists.elim` minor binder is simply unused. The resulting
/// `False` is still sound over the original `∃` assertion.
struct PreparedExists {
    p: ExprId,
    exists_ap: ExprId,
    h_exists: ExprId,
    skolem: Option<NameId>,
    assumption: Option<NameId>,
}

/// Reconstruct a **top-level existential skolemization** refutation
/// ([`crate::prove_skolem_unsat_alethe`]'s [`crate::SkolemCert`]) into a Lean proof term
/// of type `False` that the trusted [`Kernel`] type-checks — certifying the
/// otherwise-trusted skolemization step over the **original** `∃` assertions.
///
/// The embedded Alethe (the skolemized refutation) is reconstructed by the
/// existing quantifier walk to `R : False`; each existential `∃x. (= l r)`
/// becomes `Exists.{1} α p_k` (with `p_k := fun x => ⟦(= l r) x⟧`) and an honest
/// axiom `h_∃_k : Exists α p_k`. `R` is parametric in each skolem constant
/// `sk_k` and its `P(sk_k)` assumption, so it is wrapped (innermost existential
/// out) as
/// `Exists.rec α p_k (fun _ => False) (fun w hw => R[sk_k:=w, P(sk_k):=hw]) h_∃_k`.
///
/// # Errors
///
/// Returns a [`ReconstructError`] if the embedded refutation does not
/// reconstruct, if a skolem constant or its `P(sk)` assumption cannot be located
/// in the reconstructed term's environment, or if the assembled `Exists.elim`
/// term is rejected by the kernel. Never panics on malformed input.
pub fn reconstruct_skolem_unsat_proof(
    ctx: &mut ReconstructCtx,
    cert: &crate::SkolemCert,
) -> Result<ExprId, ReconstructError> {
    if cert.skolems.is_empty() {
        return Err(ReconstructError::MalformedStep {
            rule: "skolemize".to_owned(),
            detail: "certificate has no existential to certify".to_owned(),
        });
    }

    // Pre-declare each existential's predicate / proposition / honest hypothesis
    // axiom, and the **expected** `P(sk_k)` assumption proposition (used to locate
    // the assumption axiom the inner walk will declare). We declare these before
    // the inner walk so the skolem atoms are interned consistently; the inner walk
    // declares the `P(sk_k)` assumption itself.
    let mut expected_assumption: Vec<ExprId> = Vec::with_capacity(cert.skolems.len());
    let mut exists_data: Vec<(ExprId, ExprId, ExprId, String)> =
        Vec::with_capacity(cert.skolems.len());
    for rec in &cert.skolems {
        let (p, exists_ap) = ctx.mk_exists(&rec.bound_var, &rec.body)?;
        let h_exists = fresh_axiom(ctx, exists_ap, "exists")?;
        // The skolemized assumption `P(sk_k) = body[x := sk_k]`, as a closed
        // proposition `Eq α ⟦l[x:=sk]⟧ ⟦r[x:=sk]⟧`.
        let assume_prop = skolemized_assumption_prop(ctx, rec)?;
        expected_assumption.push(assume_prop);
        exists_data.push((p, exists_ap, h_exists, rec.skolem_name.clone()));
    }

    // Snapshot the "assume" axioms before the inner walk so we can identify the
    // ones the walk declares for the `P(sk_k)` units.
    let before: BTreeSet<NameId> = ctx
        .axiom_roles
        .iter()
        .filter(|(_, role)| role.as_str() == "assume")
        .map(|(&n, _)| n)
        .collect();

    // Reconstruct the skolemized refutation `R : False`.
    let refutation = reconstruct_quant_unsat_proof(ctx, &cert.commands)?;

    // Identify, per existential, the skolem-constant `NameId` (interned by the
    // walk's atom translation) and the `P(sk_k)` assumption axiom (a freshly-added
    // "assume" axiom whose type is def-eq to the expected `P(sk_k)` proposition).
    let mut prepared: Vec<PreparedExists> = Vec::with_capacity(cert.skolems.len());
    for (idx, (p, exists_ap, h_exists, skolem_name)) in exists_data.into_iter().enumerate() {
        // The skolem atom / `P(sk_k)` assumption are present iff the inner
        // refutation actually used the witness. An absent one (a vacuous
        // existential) leaves the corresponding `Exists.elim` binder unused.
        let skolem = ctx.atom_name_id(&skolem_name);
        let assumption = find_assumption_axiom(ctx, &before, expected_assumption[idx]);
        prepared.push(PreparedExists {
            p,
            exists_ap,
            h_exists,
            skolem,
            assumption,
        });
    }

    // Wrap `R` in nested `Exists.elim`s, innermost existential first. For each, a
    // fresh `w` fvar (the witness) replaces `Const(skolem)` and a fresh `hw` fvar
    // (the `p w` proof) replaces `Const(assumption)`; then `abstract_fvars` turns
    // them into the minor's two binders (unused binders are fine — a vacuous
    // existential simply does not mention `w`/`hw`).
    let mut acc = refutation;
    for pe in prepared.into_iter().rev() {
        let w_fvar = ctx.fresh_local_fvar();
        let hw_fvar = ctx.fresh_local_fvar();
        let w = ctx.kernel.fvar(w_fvar);
        let hw = ctx.kernel.fvar(hw_fvar);
        // R[skolem := w, assumption := hw] (each substitution a no-op when the
        // corresponding constant is absent).
        if let Some(skolem) = pe.skolem {
            acc = ctx.replace_const(acc, skolem, w);
        }
        if let Some(assumption) = pe.assumption {
            acc = ctx.replace_const(acc, assumption, hw);
        }
        // minor := fun (w : α) (hw : p w) => acc.
        //   `hw`'s domain `p w` is under the `w` binder ⇒ `w` is BVar 0 there.
        let w_bvar0 = ctx.kernel.bvar(0);
        let p_w_dom = ctx.kernel.app(pe.p, w_bvar0);
        // Abstract the two fvars: innermost-first ⇒ [w_fvar, hw_fvar] makes
        // `hw_fvar → BVar 0`, `w_fvar → BVar 1` in the body.
        let body = ctx.kernel.abstract_fvars(acc, &[w_fvar, hw_fvar]);
        let anon = ctx.kernel.anon();
        let inner = ctx.kernel.lam(anon, p_w_dom, body, BinderInfo::Default);
        let minor = ctx.kernel.lam(anon, ctx.alpha, inner, BinderInfo::Default);
        // Exists.rec α p (fun _ => False) minor h_∃ : False.
        acc = ctx.mk_exists_elim_false(pe.p, pe.exists_ap, minor, pe.h_exists);
    }

    check_false(ctx, acc)
}

/// The closed proposition `Eq α ⟦l[x:=sk]⟧ ⟦r[x:=sk]⟧` for a single-equality
/// existential body `(= l r)` with bound variable `x` and skolem constant `sk` —
/// the type of the `P(sk)` assumption the inner walk declares.
fn skolemized_assumption_prop(
    ctx: &mut ReconstructCtx,
    rec: &crate::SkolemRecord,
) -> Result<ExprId, ReconstructError> {
    let AletheTerm::App(head, args) = &rec.body else {
        return Err(ReconstructError::MalformedStep {
            rule: "skolemize".to_owned(),
            detail: "existential body is not an application".to_owned(),
        });
    };
    if head != "=" || args.len() != 2 {
        return Err(ReconstructError::MalformedStep {
            rule: "skolemize".to_owned(),
            detail: "existential body is not a single equality `(= l r)`".to_owned(),
        });
    }
    // Translate each operand with `bound_var ↦ Const(skolem_name)`.
    let l = subst_bound_to_skolem(ctx, &args[0], &rec.bound_var, &rec.skolem_name)?;
    let r = subst_bound_to_skolem(ctx, &args[1], &rec.bound_var, &rec.skolem_name)?;
    Ok(ctx.mk_eq(l, r))
}

/// Translate an Alethe term to a Lean `ExprId`, rendering each `Const(bound_var)`
/// as the skolem constant `Const(skolem_name)` (an EUF atom). Otherwise identical
/// to [`ReconstructCtx::alethe_term_to_expr`].
fn subst_bound_to_skolem(
    ctx: &mut ReconstructCtx,
    term: &AletheTerm,
    bound_var: &str,
    skolem_name: &str,
) -> Result<ExprId, ReconstructError> {
    match term {
        AletheTerm::Const(s) if s == bound_var => {
            let name = ctx.atom_const(skolem_name);
            Ok(ctx.kernel.const_(name, vec![]))
        }
        AletheTerm::Const(s) => {
            let name = ctx.atom_const(s);
            Ok(ctx.kernel.const_(name, vec![]))
        }
        AletheTerm::App(head, args) if head == "=" => {
            let [l, r] = args.as_slice() else {
                return Err(ReconstructError::UnsupportedTerm { term: term.key() });
            };
            let l = subst_bound_to_skolem(ctx, l, bound_var, skolem_name)?;
            let r = subst_bound_to_skolem(ctx, r, bound_var, skolem_name)?;
            Ok(ctx.mk_eq(l, r))
        }
        AletheTerm::App(head, args) if !args.is_empty() => {
            let f_name = ctx.func_const(head, args.len());
            let mut e = ctx.kernel.const_(f_name, vec![]);
            for arg in args {
                let a = subst_bound_to_skolem(ctx, arg, bound_var, skolem_name)?;
                e = ctx.kernel.app(e, a);
            }
            Ok(e)
        }
        AletheTerm::App(..) | AletheTerm::Indexed { .. } => {
            Err(ReconstructError::UnsupportedTerm { term: term.key() })
        }
    }
}

/// Find the "assume" axiom — declared by the inner refutation walk (i.e. *not*
/// already in `before`) — whose declared type is [`Kernel::def_eq`] to `expected`
/// (the `P(sk)` proposition). The skolem constants are fresh, so each `P(sk_k)`
/// type is unique among the assumptions, giving an unambiguous match.
fn find_assumption_axiom(
    ctx: &mut ReconstructCtx,
    before: &BTreeSet<NameId>,
    expected: ExprId,
) -> Option<NameId> {
    // Collect candidates deterministically (BTreeMap iteration order is by id).
    let candidates: Vec<NameId> = ctx
        .axiom_roles
        .iter()
        .filter(|(n, role)| role.as_str() == "assume" && !before.contains(*n))
        .map(|(&n, _)| n)
        .collect();
    for n in candidates {
        let ty = ctx.kernel.environment().get(n)?.ty();
        if ctx.kernel.def_eq(ty, expected) {
            return Some(n);
        }
    }
    None
}

impl ReconstructCtx {
    /// Mint a fresh free-variable id for transient `Exists.elim` binders, from the
    /// context's deterministic counter (kept well above any kernel-internal fvar
    /// by a large offset, since reconstruction otherwise builds closed terms).
    fn fresh_local_fvar(&mut self) -> u64 {
        let id = self.next_id;
        self.next_id += 1;
        // Offset into a private high range so these never alias a kernel fvar.
        id.wrapping_add(1 << 48)
    }
}

// ===========================================================================
// Propositional resolution (P3.7 slice 3) — the clausal-layer foundation.
//
// Clauses are encoded as Lean `Prop`s and resolution is reconstructed into a
// kernel-checked proof term, ultimately of type `False` for a refutation.
//
// ## The encoding
//
// - A propositional **atom** `p` (a CNF variable / Boolean atom) ⇒ an opaque
//   `Axiom : Prop` (declared lazily, deterministically, in `prop_atoms`).
// - A **literal** `p` ⇒ the Prop `p`; `(not p)` ⇒ `Not p` (= `p → False`).
// - A **clause** `(cl l1 … ln)` ⇒ the right-nested disjunction
//   `l1 ∨ (l2 ∨ … ∨ ln)`; the **empty clause `(cl)`** ⇒ `False`; a unit clause
//   `(cl l)` ⇒ just `Enc(l)`.
//
// ## Excluded middle
//
// The classical axiom `em : Π (p : Prop), Or p (Not p)` (Lean's `Classical.em`)
// is declared in the context. axeyum's solver is classical, so this is the
// faithful encoding. NOTE: the *binary* resolution reconstruction below is in
// fact constructive — it case-splits (via `Or.rec`) on a premise proof we
// already hold and discharges the pivot branch with `Not l : l → False`, so it
// never consumes `em`. `em` is declared (and reported) to make the classical
// commitment explicit and to back the general pivot-free shape if reached.
//
// ## Soundness
//
// Every reconstructed term is `infer`-checked by the trusted kernel against its
// claimed clause Prop (and the final refutation against `False`). A wrong
// resolvent fails to infer to the claimed type ⇒ `ReconstructError`, never a
// wrong `False`. The only addition to the trusted base is the `em` axiom.
// ===========================================================================

impl ReconstructCtx {
    /// Get (declaring lazily) the `Prop` constant `NameId` for a propositional
    /// atom of the clausal layer. Idempotent: the same atom name always maps to
    /// the same opaque `Axiom : Prop`.
    fn prop_atom_const(&mut self, name: &str) -> NameId {
        if let Some(&id) = self.prop_atoms.get(name) {
            return id;
        }
        let decl_name = self.fresh_name("prop");
        let prop = self.kernel.sort_zero();
        self.kernel
            .add_declaration(Declaration::Axiom {
                name: decl_name,
                uparams: vec![],
                ty: prop,
            })
            .expect("propositional atom axiom (_ : Prop) should admit");
        self.prop_atoms.insert(name.to_owned(), decl_name);
        decl_name
    }

    /// Build the Lean proposition `Or a b` (the prelude's `Or`, in `Prop`).
    fn mk_or(&mut self, a: ExprId, b: ExprId) -> ExprId {
        let or = self.kernel.const_(self.prelude.or, vec![]);
        let e = self.kernel.app(or, a);
        self.kernel.app(e, b)
    }

    /// Declare (lazily) and return the excluded-middle axiom
    /// `em : Π (p : Prop), Or p (Not p)`.
    ///
    /// # Panics
    ///
    /// Panics only if the fixed, known-good `em` axiom fails to admit, which would
    /// indicate a kernel/prelude regression rather than a caller error.
    fn em_axiom(&mut self) -> NameId {
        if let Some(id) = self.em {
            return id;
        }
        let anon = self.kernel.anon();
        let prop = self.kernel.sort_zero();
        // Π (p : Prop), Or p (Not p)  — under the binder `p` = BVar 0.
        let ty = {
            let p0 = self.kernel.bvar(0);
            let not_p = self.mk_not(p0);
            let p0b = self.kernel.bvar(0);
            let or_p = self.mk_or(p0b, not_p);
            self.kernel.pi(anon, prop, or_p, BinderInfo::Default)
        };
        let name = self.fresh_name("em");
        self.kernel
            .add_declaration(Declaration::Axiom {
                name,
                uparams: vec![],
                ty,
            })
            .expect("excluded-middle axiom em : Π (p : Prop), Or p (Not p) should admit");
        self.axiom_roles.insert(name, "em".to_owned());
        self.em = Some(name);
        name
    }

    /// Translate a propositional **literal** into its Lean `Prop`:
    /// a positive literal `p` ⇒ the atom Prop `p`; a negated `(not p)` ⇒ `Not p`.
    fn lit_to_prop(&mut self, lit: &AletheLit) -> ExprId {
        let atom = self.atom_to_prop(&lit.atom);
        if lit.negated { self.mk_not(atom) } else { atom }
    }

    /// Translate a literal **atom** term into its Lean `Prop`. A bare symbol is an
    /// opaque propositional atom; a `(not φ)` application folds to `Not (atom φ)`
    /// so the clausal `negated` flag and a syntactic `(not …)` agree.
    ///
    /// In **bit mode** (the fused bitwise `QF_BV` walk, `bridge` is `Some`) the
    /// translation is *structural* and bridge-substituting: an atom whose key names a
    /// bit-vector predicate maps to that predicate's bit-level Boolean form, and the
    /// Boolean connectives over bits (`and`/`or`/`=`/`xor`/`not`) map to the prelude
    /// connectives — so a predicate's `Prop` is definitionally its bit-level form and
    /// the bridge rules become reflexive. Outside bit mode, atoms are opaque Props.
    fn atom_to_prop(&mut self, term: &AletheTerm) -> ExprId {
        if self.bridge.is_some() {
            return self.gate_term_to_prop(term);
        }
        match term {
            AletheTerm::App(head, args) if head == "not" && args.len() == 1 => {
                let inner = self.atom_to_prop(&args[0]);
                self.mk_not(inner)
            }
            AletheTerm::Const(symbol) => {
                let name = self.prop_atom_const(symbol);
                self.kernel.const_(name, vec![])
            }
            // Any compound atom (e.g. `(= a b)`, `(f x)`) is treated opaquely as a
            // single propositional atom keyed by its s-expression — sound for the
            // clausal layer, where atoms are uninterpreted Props.
            other => {
                let name = self.prop_atom_const(&other.key());
                self.kernel.const_(name, vec![])
            }
        }
    }

    /// Translate a whole **clause** into its Lean `Prop` encoding: the empty
    /// clause ⇒ `False`; a unit clause ⇒ its single literal's Prop; otherwise the
    /// right-nested disjunction `l1 ∨ (l2 ∨ … ∨ ln)`.
    fn clause_to_prop(&mut self, clause: &[AletheLit]) -> ExprId {
        let Some((last, rest)) = clause.split_last() else {
            // Empty clause ⇒ False.
            return self.kernel.const_(self.prelude.false_, vec![]);
        };
        let mut acc = self.lit_to_prop(last);
        for lit in rest.iter().rev() {
            let head = self.lit_to_prop(lit);
            acc = self.mk_or(head, acc);
        }
        acc
    }
}

/// A clausal premise during the resolution walk: its literals (for computing the
/// pivot and resolvent structurally) and a kernel proof term of the clause's
/// `Prop` encoding.
#[derive(Clone)]
struct Clause {
    lits: Vec<AletheLit>,
    proof: ExprId,
}

/// Reconstruct a propositional-**resolution** Alethe proof into a Lean proof term
/// of type `False` that the trusted [`Kernel`] type-checks.
///
/// This is the clausal-layer foundation shared by all clausal proofs (`QF_BV`,
/// SAT).
/// It walks the `Vec<AletheCommand>` shape the clausal emitter produces:
///
/// - **`assume (cl l1 … ln)`** ⇒ a fresh hypothesis `Axiom` of the clause's `Prop`
///   encoding (`l1 ∨ … ∨ ln`, or `False` for `(cl)`, or `Enc(l)` for a unit), and
///   the assumption is recorded under its id.
/// - **`or`** (the emitter's unpacking of an `assume (or φ…)` disjunction into the
///   clause `(cl φ…)`) ⇒ the premise's proof is reused verbatim: the disjunction
///   `(or φ…)` and the clause `(cl φ…)` have the **same** right-nested `Or`
///   encoding, so the unpacking is the identity on the proof term (checked by the
///   kernel against the conclusion).
/// - **`resolution` / `th_resolution`** ⇒ reconstructed by repeated **binary
///   resolution**: the step's premises are resolved pairwise (left fold) on the
///   unique complementary literal of each successive pair, building the conclusion
///   clause's proof; a conclusion of the empty clause `(cl)` yields a term of type
///   `False` (via `binary_resolve_on`, the Davis–Putnam pairwise resolvent).
///
/// The final term — the proof of the conclusion of the step deriving `(cl)` — is
/// `infer`-checked against the prelude's `False`. A wrong reconstruction makes
/// that gate fail, so this returns an error, never a wrong `False`.
///
/// # Errors
///
/// Returns a [`ReconstructError`] for an unknown premise id, an unsupported
/// command/rule shape, a resolution whose premises do not have the expected
/// single complementary pivot, a proof that never derives the empty clause, or a
/// kernel rejection. It never panics on malformed or out-of-scope input.
pub fn reconstruct_resolution_proof(
    ctx: &mut ReconstructCtx,
    commands: &[AletheCommand],
) -> Result<ExprId, ReconstructError> {
    // Declare `em` up front so the classical commitment is recorded even when the
    // (constructive) binary path does not consume it.
    let _ = ctx.em_axiom();

    let mut env: BTreeMap<String, Clause> = BTreeMap::new();

    for cmd in commands {
        match cmd {
            AletheCommand::Assume { id, clause } => {
                let prop = ctx.clause_to_prop(clause);
                let proof = fresh_axiom(ctx, prop, "assume")?;
                env.insert(
                    id.clone(),
                    Clause {
                        lits: clause.clone(),
                        proof,
                    },
                );
            }
            AletheCommand::Step {
                id,
                clause,
                rule,
                premises,
                ..
            } => match rule.as_str() {
                // `or` unpacks an assumed disjunction into clause form; the `Prop`
                // encodings coincide, so the proof passes through unchanged (and is
                // kernel-checked against the conclusion encoding).
                "or" => {
                    let [p] = premises.as_slice() else {
                        return Err(ReconstructError::UnsupportedResolution {
                            detail: format!(
                                "`or` step expects exactly one premise, found {}",
                                premises.len()
                            ),
                        });
                    };
                    let premise = lookup(&env, p)?;
                    let expected = ctx.clause_to_prop(clause);
                    let proof = check_against(ctx, "or", premise.proof, expected)?;
                    env.insert(
                        id.clone(),
                        Clause {
                            lits: clause.clone(),
                            proof,
                        },
                    );
                }
                "resolution" | "th_resolution" => {
                    let resolved = reconstruct_resolution_step(ctx, clause, premises, &env)?;
                    if clause.is_empty() {
                        // The empty clause: this is the refutation close. Validate the
                        // term against `False` and return it.
                        return check_false_prop(ctx, resolved.proof);
                    }
                    // A non-empty resolvent: kernel-check it against the stated
                    // conclusion encoding, then record it for later steps.
                    let expected = ctx.clause_to_prop(clause);
                    let proof = check_against(ctx, rule, resolved.proof, expected)?;
                    env.insert(
                        id.clone(),
                        Clause {
                            lits: clause.clone(),
                            proof,
                        },
                    );
                }
                other => {
                    return Err(ReconstructError::UnsupportedRule {
                        rule: other.to_owned(),
                    });
                }
            },
        }
    }

    Err(ReconstructError::NoEmptyClause)
}

/// Look up a premise clause by id, erroring with [`ReconstructError::UnknownPremise`]
/// when it was never defined.
fn lookup<'a>(env: &'a BTreeMap<String, Clause>, id: &str) -> Result<&'a Clause, ReconstructError> {
    env.get(id)
        .ok_or_else(|| ReconstructError::UnknownPremise { id: id.to_owned() })
}

/// Reconstruct one `resolution`/`th_resolution` step by folding **binary
/// resolution** across its premises.
///
/// A single premise passes through. For ≥2 premises the running accumulator is
/// resolved against the premises one at a time — but **not** strictly in premise
/// order: Alethe/LRAT resolution chains (the real emitter's RUP-hint order) do not
/// guarantee that consecutive premises share a pivot. So at each step we pick, from
/// the remaining premises, one that *is* complementary-resolvable with the current
/// accumulator (a greedy unit-propagation-style schedule). This reorders the chain
/// into a resolvable sequence without changing the constructive binary core; if no
/// remaining premise resolves with the accumulator, the step is rejected.
///
/// The returned [`Clause`] carries the resolvent literals and its kernel proof term.
///
/// Pool-size budget for the Davis–Putnam working set: DP is worst-case exponential,
/// so cap the pool and degrade to a clean error rather than hang/OOM on a
/// pathological proof.
const DP_POOL_BUDGET: usize = 4096;

fn reconstruct_resolution_step(
    ctx: &mut ReconstructCtx,
    conclusion: &[AletheLit],
    premises: &[String],
    env: &BTreeMap<String, Clause>,
) -> Result<Clause, ReconstructError> {
    let Some((first, rest)) = premises.split_first() else {
        return Err(ReconstructError::UnsupportedResolution {
            detail: "resolution step has no premises".to_owned(),
        });
    };
    // Polarity-normalize every clause first so a `+(not X)` literal and a `-X`
    // literal — the same `Not ⟦X⟧` Prop, spelled inconsistently by the upstream CNF
    // — match as complementary pivots in `find_pivot`. Soundness is unchanged:
    // normalization preserves `clause_to_prop`, so each clause `proof` stays
    // well-typed, and every `binary_resolve` below is kernel-checked.
    let normalized = |c: &Clause| Clause {
        lits: c.lits.iter().map(normalize_lit_polarity).collect(),
        proof: c.proof,
    };
    // **Davis–Putnam resolution.** The refutation is a resolution DAG, not a chain
    // (a pivot from one premise cancels against another, not a running
    // accumulator), so any accumulator/greedy/pool fold dead-ends by consuming a
    // clause another subtree needs. Instead, eliminate every **non-conclusion**
    // variable: partition the pool on the variable and replace it with all
    // `pos × neg` resolvents (dropping tautologies). DP is complete for the
    // implied clause, so what remains is the conclusion (the empty clause for a
    // closing refutation). Every `binary_resolve_on` is kernel-checked.
    let conclusion_keys: std::collections::BTreeSet<String> = conclusion
        .iter()
        .map(|l| normalize_lit_polarity(l).atom.key())
        .collect();

    let mut pool: Vec<Clause> = std::iter::once(Ok(normalized(lookup(env, first)?)))
        .chain(rest.iter().map(|p| Ok(normalized(lookup(env, p)?))))
        .collect::<Result<_, ReconstructError>>()?;

    loop {
        // Count, for each non-conclusion variable, how many pool clauses hold it
        // positively vs negatively (each clause counted once per variable).
        let mut counts: std::collections::BTreeMap<String, (usize, usize)> =
            std::collections::BTreeMap::new();
        for c in &pool {
            let mut seen: std::collections::BTreeSet<String> = std::collections::BTreeSet::new();
            for l in &c.lits {
                let k = l.atom.key();
                if conclusion_keys.contains(&k) || !seen.insert(k.clone()) {
                    continue;
                }
                let e = counts.entry(k).or_insert((0, 0));
                if l.negated {
                    e.1 += 1;
                } else {
                    e.0 += 1;
                }
            }
        }
        // Eliminate the variable with the fewest resolvents (`pos × neg`) — the
        // standard Davis–Putnam ordering heuristic that keeps the working set small
        // on structured proofs. Order does not affect correctness (DP is complete),
        // only cost.
        let pivot = counts
            .iter()
            .filter(|(_, (p, n))| *p > 0 && *n > 0)
            .min_by_key(|(_, (p, n))| p * n)
            .map(|(k, _)| k.clone());
        let Some(pivot) = pivot else { break };

        let mut pos: Vec<Clause> = Vec::new();
        let mut neg: Vec<Clause> = Vec::new();
        let mut without: Vec<Clause> = Vec::new();
        for c in std::mem::take(&mut pool) {
            match c.lits.iter().find(|l| l.atom.key() == pivot) {
                Some(l) if !l.negated => pos.push(c),
                Some(_) => neg.push(c),
                None => without.push(c),
            }
        }
        pool = without;
        for p in &pos {
            for n in &neg {
                if let Some(r) = binary_resolve_on(ctx, p, n, &pivot, true)? {
                    // Skip a resolvent already present (cheap subsumption-of-equals).
                    let key = clause_key(&r.lits);
                    if !pool.iter().any(|c| clause_key(&c.lits) == key) {
                        pool.push(r);
                    }
                }
            }
        }
        if pool.len() > DP_POOL_BUDGET {
            return Err(ReconstructError::UnsupportedResolution {
                detail: format!(
                    "Davis–Putnam working set exceeded {DP_POOL_BUDGET} clauses \
                     (proof too large for inlined resolution reconstruction)"
                ),
            });
        }
        if pool.is_empty() {
            return Err(ReconstructError::UnsupportedResolution {
                detail: format!("eliminating `{pivot}` left no clauses"),
            });
        }
    }

    // Every remaining clause has only conclusion literals. Return the one whose
    // literal set matches the conclusion (the empty clause for a closing step).
    let want = normalize_clause_key(conclusion);
    pool.into_iter()
        .find(|c| normalize_clause_key(&c.lits) == want)
        .ok_or_else(|| ReconstructError::UnsupportedResolution {
            detail: format!("resolution did not derive the conclusion `{want}`"),
        })
}

/// A clause's identity key under polarity-normalization, order-independent (sorted
/// `±atom-key` set) — used to compare a derived clause against the step conclusion.
fn normalize_clause_key(lits: &[AletheLit]) -> String {
    let mut parts: Vec<String> = lits
        .iter()
        .map(|l| {
            let n = normalize_lit_polarity(l);
            format!("{}{}", if n.negated { "-" } else { "+" }, n.atom.key())
        })
        .collect();
    parts.sort();
    parts.dedup();
    parts.join(",")
}

/// Canonicalize a literal's polarity by peeling leading `(not …)` atoms into the
/// `negated` flag: `+(not X)` becomes `-X`, `-(not X)` becomes `+X`. The upstream
/// CNF spells some negations as the flag and some as a `(not …)` atom; a positive
/// `(not X)` literal and a negative `X` literal denote the same Prop (`Not ⟦X⟧`),
/// so this leaves [`ReconstructCtx::clause_to_prop`] (and the clause `proof` type)
/// unchanged while letting complementary literals match in [`find_pivot`].
fn normalize_lit_polarity(lit: &AletheLit) -> AletheLit {
    let mut atom = lit.atom.clone();
    let mut negated = lit.negated;
    while let AletheTerm::App(head, args) = &atom {
        if head == "not" && args.len() == 1 {
            let inner = args[0].clone();
            atom = inner;
            negated = !negated;
        } else {
            break;
        }
    }
    AletheLit { atom, negated }
}

/// Push `lit` onto `out` unless a literal of the same atom key and polarity is
/// already present (first-seen-order de-duplication for the resolvent).
fn push_unique(lit: &AletheLit, out: &mut Vec<AletheLit>) {
    let k = (lit.atom.key(), lit.negated);
    if !out.iter().any(|o| (o.atom.key(), o.negated) == k) {
        out.push(lit.clone());
    }
}

/// Build the binary resolvent of clause proofs `hC : Enc(C)` and `hD : Enc(D)` on
/// a **specific** pivot atom (`pivot_key`; `c_has_pos` says `c` holds it
/// positively), proving `Enc(R)` where `R = (C \ {l}) ∪ (D \ {¬l})`.
///
/// This is **constructive**: we case-split (via `Or.rec`) on the premise that
/// carries `l` positively, then on its complement discharge the pivot branch with
/// `¬l : l → False` (`False.rec`) and inject every surviving literal into `Enc(R)`
/// with `Or.inl`/`Or.inr`. No excluded middle is needed.
///
/// Returns `Ok(None)` when the resolvent is a tautology (contains some atom both
/// positively and negatively) — useless, and dropped by Davis–Putnam. Otherwise
/// builds the kernel-checked resolvent clause and its proof.
fn binary_resolve_on(
    ctx: &mut ReconstructCtx,
    c: &Clause,
    d: &Clause,
    pivot_key: &str,
    c_has_pos: bool,
) -> Result<Option<Clause>, ReconstructError> {
    // Orient: `pos` is the clause with the pivot positive, `neg` with `¬pivot`.
    let (pos, neg) = if c_has_pos { (c, d) } else { (d, c) };

    // The resolvent literal list: survivors of `pos` (drop positive pivot) then
    // survivors of `neg` (drop negative pivot), de-duplicated by key+polarity in
    // first-seen order.
    let mut resolvent: Vec<AletheLit> = Vec::new();
    for lit in &pos.lits {
        if lit.atom.key() != pivot_key || lit.negated {
            push_unique(lit, &mut resolvent);
        }
    }
    for lit in &neg.lits {
        if lit.atom.key() != pivot_key || !lit.negated {
            push_unique(lit, &mut resolvent);
        }
    }

    // A tautological resolvent (some atom appears both `+` and `-`) is dropped.
    let tautological = resolvent.iter().any(|l| {
        let k = l.atom.key();
        resolvent
            .iter()
            .any(|o| o.atom.key() == k && o.negated != l.negated)
    });
    if tautological {
        return Ok(None);
    }

    // The target Prop `Enc(R)`.
    let r_prop = ctx.clause_to_prop(&resolvent);

    // `neg`-handler: a proof of the pivot `hp : pivot` produces a proof of
    // `Enc(R)` from `neg`'s proof, by case-splitting on `Enc(neg)`. For neg's
    // pivot literal `¬pivot : pivot → False` we get `False`, discharged by
    // `False.rec` into `Enc(R)`; every other literal is injected into `Enc(R)`.
    //
    // We build it as a closed term consuming `hp` and `neg.proof` directly (no
    // binder games): `neg_to_r(hp) : Enc(R)`.
    let neg_to_r = |ctx: &mut ReconstructCtx, hp: ExprId| -> Result<ExprId, ReconstructError> {
        clause_elim(
            ctx,
            neg,
            r_prop,
            &resolvent,
            &|ctx, lit, lit_proof, resolvent| {
                if lit.atom.key() == pivot_key && lit.negated {
                    // lit_proof : Not pivot = pivot → False. Apply to hp, then False.rec.
                    let false_app = ctx.kernel.app(lit_proof, hp);
                    Ok(ex_falso(ctx, r_prop, false_app))
                } else {
                    inject_lit(ctx, lit, lit_proof, resolvent)
                }
            },
        )
    };

    // `pos`-handler: case-split on `Enc(pos)`. For pos's pivot literal
    // `hp : pivot` we run `neg_to_r(hp)`; every other literal is injected.
    let proof = clause_elim(
        ctx,
        pos,
        r_prop,
        &resolvent,
        &|ctx, lit, lit_proof, resolvent| {
            if lit.atom.key() == pivot_key && !lit.negated {
                neg_to_r(ctx, lit_proof)
            } else {
                inject_lit(ctx, lit, lit_proof, resolvent)
            }
        },
    )?;

    Ok(Some(Clause {
        lits: resolvent,
        proof,
    }))
}

/// `False.rec`-eliminate a `False` proof into the target Prop `target`:
/// `False.rec.{0} (fun _ => target) h_false : target`.
fn ex_falso(ctx: &mut ReconstructCtx, target: ExprId, h_false: ExprId) -> ExprId {
    let anon = ctx.kernel.anon();
    let false_const = ctx.kernel.const_(ctx.prelude.false_, vec![]);
    // motive := fun (_ : False) => target.
    let motive = ctx
        .kernel
        .lam(anon, false_const, target, BinderInfo::Default);
    let z = ctx.kernel.level_zero();
    let rec = ctx.kernel.const_(ctx.prelude.false_rec, vec![z]);
    let e = ctx.kernel.app(rec, motive);
    ctx.kernel.app(e, h_false)
}

/// Inject a single literal proof `lit_proof : Enc(lit)` into the resolvent's `Or`
/// encoding `Enc(resolvent)`, by the `Or.inl`/`Or.inr` nesting that reaches
/// `lit`'s position. `lit` must occur in `resolvent` (matched by key+polarity);
/// otherwise this is a malformed reconstruction and a [`ReconstructError`] fires.
fn inject_lit(
    ctx: &mut ReconstructCtx,
    lit: &AletheLit,
    lit_proof: ExprId,
    resolvent: &[AletheLit],
) -> Result<ExprId, ReconstructError> {
    let want = (lit.atom.key(), lit.negated);
    let idx = resolvent
        .iter()
        .position(|o| (o.atom.key(), o.negated) == want)
        .ok_or_else(|| ReconstructError::UnsupportedResolution {
            detail: format!("literal `{}` not found in resolvent", lit.atom.key()),
        })?;

    // The resolvent is right-nested: `l0 ∨ (l1 ∨ (… ∨ l_{n-1}))`. At index `idx`,
    // the sub-encoding `tail_i = Enc(resolvent[i..])` is reached by `idx` `Or.inr`s,
    // then (if `idx` is not the last literal) a final `Or.inl` carries `lit`.
    let n = resolvent.len();
    debug_assert!(n >= 1);

    // Build the proof bottom-up over the tail suffixes. We need, for each suffix
    // starting at `i`, the Props of `head_i = Enc(resolvent[i])` and
    // `tail_{i+1} = Enc(resolvent[i+1..])` to type the `Or.inl`/`Or.inr` ctors.
    let mut proof = lit_proof;
    // `i` walks from `idx` back to 0, wrapping the running proof.
    for i in (0..=idx).rev() {
        if i == idx {
            // Innermost: place `lit_proof` at position `idx`.
            if idx == n - 1 {
                // Last literal: the suffix `Enc(resolvent[idx..])` is just `Enc(lit)`.
                // proof already has that type; nothing to wrap.
            } else {
                // `Enc(resolvent[idx..]) = head_idx ∨ tail_{idx+1}`; use `Or.inl`.
                let a = ctx.lit_to_prop(&resolvent[idx]);
                let b = ctx.clause_to_prop(&resolvent[idx + 1..]);
                proof = or_inl(ctx, a, b, proof);
            }
        } else {
            // Wrap: `Enc(resolvent[i..]) = head_i ∨ tail_{i+1}`; we have a proof of
            // `tail_{i+1}` (the running `proof`); use `Or.inr`.
            let a = ctx.lit_to_prop(&resolvent[i]);
            let b = ctx.clause_to_prop(&resolvent[i + 1..]);
            proof = or_inr(ctx, a, b, proof);
        }
    }
    Ok(proof)
}

/// `Or.inl.{0} a b h : Or a b` from `h : a`.
fn or_inl(ctx: &mut ReconstructCtx, a: ExprId, b: ExprId, h: ExprId) -> ExprId {
    let inl = ctx.kernel.const_(ctx.prelude.or_inl, vec![]);
    let e = ctx.kernel.app(inl, a);
    let e = ctx.kernel.app(e, b);
    ctx.kernel.app(e, h)
}

/// `Or.inr.{0} a b h : Or a b` from `h : b`.
fn or_inr(ctx: &mut ReconstructCtx, a: ExprId, b: ExprId, h: ExprId) -> ExprId {
    let inr = ctx.kernel.const_(ctx.prelude.or_inr, vec![]);
    let e = ctx.kernel.app(inr, a);
    let e = ctx.kernel.app(e, b);
    ctx.kernel.app(e, h)
}

/// Eliminate a clause proof `clause.proof : Enc(clause)` into the target Prop
/// `target`, by running `per_lit` on each literal's hypothesis to produce a proof
/// of `target`, threaded through the right-nested `Or` via `Or.rec`.
///
/// For a unit clause this is `per_lit(l0, clause.proof)`. For `l0 ∨ rest`, it is
/// `Or.rec.{0} A B (fun _ => target) (fun (h0 : A) => per_lit(l0, h0))
///   (fun (hr : B) => <recurse on rest>) clause.proof`, where the minor premises
/// are built as closed lambdas (so the hypothesis flows in as `BVar 0`, then is
/// instantiated through `per_lit`/recursion as an `fvar`-free term).
///
/// `per_lit(ctx, lit, lit_proof, resolvent)` receives the literal, a proof term
/// of `Enc(lit)`, and the resolvent literal list (so it can inject), and returns a
/// proof of `target`.
fn clause_elim(
    ctx: &mut ReconstructCtx,
    clause: &Clause,
    target: ExprId,
    resolvent: &[AletheLit],
    per_lit: &PerLit<'_>,
) -> Result<ExprId, ReconstructError> {
    clause_elim_inner(ctx, &clause.lits, clause.proof, target, resolvent, per_lit)
}

/// The per-literal handler for [`clause_elim`]: given the literal, a proof of its
/// `Enc(lit)`, and the resolvent literal list, produce a proof of the target Prop.
type PerLit<'a> = dyn Fn(&mut ReconstructCtx, &AletheLit, ExprId, &[AletheLit]) -> Result<ExprId, ReconstructError>
    + 'a;

/// The recursive worker for [`clause_elim`] over a literal suffix with proof
/// `proof : Enc(lits)`.
fn clause_elim_inner(
    ctx: &mut ReconstructCtx,
    lits: &[AletheLit],
    proof: ExprId,
    target: ExprId,
    resolvent: &[AletheLit],
    per_lit: &PerLit<'_>,
) -> Result<ExprId, ReconstructError> {
    match lits {
        [] => Err(ReconstructError::UnsupportedResolution {
            detail: "empty clause has no literal to eliminate".to_owned(),
        }),
        // Unit suffix: `proof : Enc(l0)` directly.
        [l0] => per_lit(ctx, l0, proof, resolvent),
        // `l0 ∨ rest`: case-split with `Or.rec`.
        [l0, rest @ ..] => {
            let anon = ctx.kernel.anon();
            let a = ctx.lit_to_prop(l0); // Enc(l0)
            let b = ctx.clause_to_prop(rest); // Enc(rest)

            // minor_inl := fun (h0 : A) => per_lit(l0, h0).
            // Build the body with the hypothesis as a free variable so `per_lit`
            // produces a closed term, then abstract it back to a `BVar 0` lambda.
            let fvar_id = fresh_fvar_id(ctx);
            let h0 = ctx.kernel.fvar(fvar_id);
            let body_inl = per_lit(ctx, l0, h0, resolvent)?;
            let body_inl = ctx.kernel.abstract_fvars(body_inl, &[fvar_id]);
            let minor_inl = ctx.kernel.lam(anon, a, body_inl, BinderInfo::Default);

            // minor_inr := fun (hr : B) => <recurse on rest with hr>.
            let fvar_id2 = fresh_fvar_id(ctx);
            let hr = ctx.kernel.fvar(fvar_id2);
            let body_inr = clause_elim_inner(ctx, rest, hr, target, resolvent, per_lit)?;
            let body_inr = ctx.kernel.abstract_fvars(body_inr, &[fvar_id2]);
            let minor_inr = ctx.kernel.lam(anon, b, body_inr, BinderInfo::Default);

            // motive := fun (_ : Or A B) => target.
            let or_ab = ctx.mk_or(a, b);
            let motive = ctx.kernel.lam(anon, or_ab, target, BinderInfo::Default);

            // Or.rec.{0} A B motive minor_inl minor_inr proof : target.
            let z = ctx.kernel.level_zero();
            let rec = ctx.kernel.const_(ctx.prelude.or_rec, vec![z]);
            let e = ctx.kernel.app(rec, a);
            let e = ctx.kernel.app(e, b);
            let e = ctx.kernel.app(e, motive);
            let e = ctx.kernel.app(e, minor_inl);
            let e = ctx.kernel.app(e, minor_inr);
            Ok(ctx.kernel.app(e, proof))
        }
    }
}

/// Mint a fresh free-variable id for building open `Or.rec` minor-premise bodies.
/// Reuses the deterministic `next_id` counter, offset into a private range so it
/// never collides with declaration-name numbering semantics.
fn fresh_fvar_id(ctx: &mut ReconstructCtx) -> u64 {
    let id = ctx.next_id;
    ctx.next_id += 1;
    id
}

/// The soundness gate for the final propositional refutation term: `infer` it and
/// require the inferred type to be [`Kernel::def_eq`] to the prelude's `False`.
fn check_false_prop(ctx: &mut ReconstructCtx, proof: ExprId) -> Result<ExprId, ReconstructError> {
    let false_ = ctx.kernel.const_(ctx.prelude.false_, vec![]);
    check_against(ctx, "resolution", proof, false_)
}

// ===========================================================================
// Tseitin CNF-introduction rules (P3.7 slice 4) — the Boolean-gate layer.
//
// These are the premise-free Alethe rules `and_pos`/`and_neg`/`or_pos`/`or_neg`,
// `equiv_pos1`/`equiv_pos2`/`equiv_neg1`/`equiv_neg2`, and
// `xor_pos1`/`xor_pos2`/`xor_neg1`/`xor_neg2`. Each concludes a propositional
// **tautology** clause over the structured logical gate (`And`/`Or`/`Iff`/`Not`)
// of its operand atoms — the clauses a Tseitin encoding emits to connect a
// Boolean gate to its defining clauses. axeyum's QF_BV proofs use these to link
// the bit-blasted gate layer to the clausal (resolution) layer.
//
// ## The gate encoding
//
// Unlike the opaque clausal `atom_to_prop`, these rules are *about* gate
// structure, so a gate literal is translated **structurally**:
//
// - `(and t…)` ⇒ `And ⟦t0⟧ (And ⟦t1⟧ …)` (right-nested for n-ary);
// - `(or t…)`  ⇒ `Or  ⟦t0⟧ (Or  ⟦t1⟧ …)` (right-nested);
// - `(not t)`  ⇒ `Not ⟦t⟧`;
// - `(= a b)`  ⇒ `Iff ⟦a⟧ ⟦b⟧` (a Boolean equality, i.e. an iff — the gate
//   operands in the Tseitin layer are bits);
// - `(xor a b)` ⇒ `Not (Iff ⟦a⟧ ⟦b⟧)` — **the xor modeling choice** (xor is the
//   negation of iff). This is consistent across all four `xor_*` rules.
// - anything else (a bare symbol, or a compound axeyum keys opaquely, e.g.
//   `((_ @bit_of i) x)`) ⇒ an opaque propositional atom (via `prop_atoms`).
//
// ## How each tautology is proved
//
// Every conclusion clause is a propositional tautology over its operand atoms.
// We prove it **uniformly**: case-split (classically, via `em`) on every
// distinct operand atom of the clause, and in each of the resulting truth
// assignments find a clause literal that is satisfied and inject its proof into
// the right-nested `Or` encoding. The per-literal proof is a structural
// truth/falsity evaluator over the gate (`prove_term_true`/`prove_term_false`):
// e.g. `And A B` is true by `And.intro` when both hold, and false by
// `fun h => hnA (And.rec … h)` when an operand is false.
//
// ## Soundness
//
// The kernel is the gate: the assembled proof term is `infer`-checked and
// `def_eq`-compared against the clause's `Or`-encoding (`gate_clause_to_prop`).
// A wrong conclusion (a mis-selected conjunct, a swapped polarity) makes the
// satisfied-literal search fail in some leaf, or the final `infer`/`def_eq`
// reject — never a wrong "checked". `em` (already in the context) is the only
// classical addition.
// ===========================================================================

impl ReconstructCtx {
    /// Build the Lean proposition `And a b` (the prelude's `And`, in `Prop`).
    fn mk_and(&mut self, a: ExprId, b: ExprId) -> ExprId {
        let and = self.kernel.const_(self.prelude.and, vec![]);
        let e = self.kernel.app(and, a);
        self.kernel.app(e, b)
    }

    /// Build the Lean proposition `Iff a b` (the prelude's `Iff`, in `Prop`).
    fn mk_iff(&mut self, a: ExprId, b: ExprId) -> ExprId {
        let iff = self.kernel.const_(self.prelude.iff, vec![]);
        let e = self.kernel.app(iff, a);
        self.kernel.app(e, b)
    }

    /// Translate a **gate** term into its *structured* Lean `Prop`. Boolean
    /// connectives map to the prelude connectives applied to the translated
    /// operands; everything else is an opaque propositional atom (shared with the
    /// clausal layer's `prop_atoms`).
    ///
    /// `(and …)`/`(or …)` are right-nested for n-ary arity; `(= a b)` is `Iff`;
    /// `(xor a b)` is `Not (Iff a b)`.
    ///
    /// In **bit mode** an atom whose s-expression key is a registered bit-vector
    /// predicate is first rewritten to its bit-level Boolean form `B` (via the
    /// `bridge` map) and then translated structurally — so the predicate `Prop`
    /// *is* its bit form. The substitution fires before the structural match, so
    /// e.g. `(= (bvand a b) a)` becomes `B`'s `And`/`Iff` tree, not an `Iff` over
    /// the opaque bit-vector terms.
    fn gate_term_to_prop(&mut self, term: &AletheTerm) -> ExprId {
        let key = term.key();
        if let Some(&cached) = self.gate_memo.get(&key) {
            return cached;
        }
        let result = self.gate_term_to_prop_inner(term);
        self.gate_memo.insert(key, result);
        result
    }

    fn gate_term_to_prop_inner(&mut self, term: &AletheTerm) -> ExprId {
        if let Some(bridge) = &self.bridge {
            if let Some(b_form) = bridge.get(&term.key()) {
                let b_form = b_form.clone();
                return self.gate_term_to_prop(&b_form);
            }
        }
        match term {
            AletheTerm::App(head, args) if head == "not" && args.len() == 1 => {
                let inner = self.gate_term_to_prop(&args[0]);
                self.mk_not(inner)
            }
            AletheTerm::App(head, args) if head == "and" && !args.is_empty() => {
                self.fold_right(args, ReconstructCtx::mk_and)
            }
            AletheTerm::App(head, args) if head == "or" && !args.is_empty() => {
                self.fold_right(args, ReconstructCtx::mk_or)
            }
            AletheTerm::App(head, args) if head == "=" && args.len() == 2 => {
                let a = self.gate_term_to_prop(&args[0]);
                let b = self.gate_term_to_prop(&args[1]);
                self.mk_iff(a, b)
            }
            AletheTerm::App(head, args) if head == "xor" && args.len() == 2 => {
                let a = self.gate_term_to_prop(&args[0]);
                let b = self.gate_term_to_prop(&args[1]);
                let iff = self.mk_iff(a, b);
                self.mk_not(iff)
            }
            // The Boolean literals map to the prelude `True`/`False` (agreeing with
            // `gadget_bit_to_prop`), so a constant operand's bit — `true`/`false` from
            // `operand_bit_term` — renders identically whether it reaches here
            // directly or embedded in a gate.
            AletheTerm::Const(s) if s == "true" => self.kernel.const_(self.prelude.true_, vec![]),
            AletheTerm::Const(s) if s == "false" => self.kernel.const_(self.prelude.false_, vec![]),
            // A bit projection `((_ @bit_of i) operand)`. When `operand` is a COMPOUND
            // bit-vector term (the projection-based emission's gadget bits, e.g.
            // `((_ @bit_of i) (bvor a b))`), resolve it through the faithful bit model
            // `bv_bit` so it agrees structurally with the LHS expansion — this is the
            // reconstruction half of Carcara's projection (`build_term_vec`) scheme. A
            // bare-symbol / `#b…`-literal operand keeps the opaque/`True`/`False` leaf
            // (matching `bv_bit`'s own leaf handling), so the two sides still coincide.
            AletheTerm::Indexed { op, indices, args }
                if op == "@bit_of"
                    && indices.len() == 1
                    && args.len() == 1
                    && bit_of_operand_resolves(&args[0]) =>
            {
                if let Ok(i) = usize::try_from(indices[0]) {
                    // Reuse the `bv_bit` faithful model — for a compound operand it
                    // expands structurally; for a `#b…` literal operand it yields the
                    // constant `True`/`False` bit. (The emitter's `build_term_vec`
                    // projects `((_ @bit_of i) #b…)` for a constant concat operand.)
                    // Any failure (out-of-range bit, unsupported op) falls through to
                    // the opaque atom below.
                    if let Ok(prop) = bv_bit(self, &args[0], i) {
                        return prop;
                    }
                }
                let name = self.prop_atom_const(&term.key());
                self.kernel.const_(name, vec![])
            }
            // A bare symbol or any opaque compound: an uninterpreted Prop atom.
            other => {
                let name = self.prop_atom_const(&other.key());
                self.kernel.const_(name, vec![])
            }
        }
    }

    /// Right-fold a non-empty operand slice with a binary connective builder:
    /// `[t0, t1, …, tn]` ⇒ `op(⟦t0⟧, op(⟦t1⟧, … ⟦tn⟧))`.
    fn fold_right(
        &mut self,
        args: &[AletheTerm],
        op: fn(&mut ReconstructCtx, ExprId, ExprId) -> ExprId,
    ) -> ExprId {
        let (last, rest) = args
            .split_last()
            .expect("fold_right requires a non-empty operand slice");
        let mut acc = self.gate_term_to_prop(last);
        for t in rest.iter().rev() {
            let head = self.gate_term_to_prop(t);
            acc = op(self, head, acc);
        }
        acc
    }

    /// Translate a gate **literal** into its Lean `Prop`: a positive literal `t`
    /// ⇒ `⟦t⟧`; a negated `(not t)` ⇒ `Not ⟦t⟧`.
    fn gate_lit_to_prop(&mut self, lit: &AletheLit) -> ExprId {
        let atom = self.gate_term_to_prop(&lit.atom);
        if lit.negated { self.mk_not(atom) } else { atom }
    }

    /// Translate a whole gate **clause** into its right-nested `Or` encoding —
    /// the same shape as `clause_to_prop`, but with gate literals translated
    /// structurally (`gate_lit_to_prop`) rather than opaquely. The empty clause ⇒
    /// `False`; a unit clause ⇒ its single literal's Prop.
    fn gate_clause_to_prop(&mut self, clause: &[AletheLit]) -> ExprId {
        let Some((last, rest)) = clause.split_last() else {
            return self.kernel.const_(self.prelude.false_, vec![]);
        };
        let mut acc = self.gate_lit_to_prop(last);
        for lit in rest.iter().rev() {
            let head = self.gate_lit_to_prop(lit);
            acc = self.mk_or(head, acc);
        }
        acc
    }
}

/// A truth assignment over operand atoms: each atom's s-expression key maps to
/// its structured `Prop` and a witness — either a proof of the Prop (`true`) or a
/// proof of its `Not` (`false`).
struct Assignment {
    /// atom key → (its `Prop`, witness proof, whether the witness proves the Prop
    /// (`true`) or its negation (`false`)).
    map: BTreeMap<String, (ExprId, ExprId, bool)>,
}

impl Assignment {
    fn new() -> Self {
        Self {
            map: BTreeMap::new(),
        }
    }
}

/// The right-nested `And` `Prop` of `props` (non-empty), matching how
/// [`ReconstructCtx::gate_term_to_prop`] renders `(and φ…)` via `fold_right`.
fn and_chain_prop_of(ctx: &mut ReconstructCtx, props: &[ExprId]) -> ExprId {
    let mut it = props.iter().rev().copied();
    let mut acc = it.next().expect("and has at least one operand");
    for p in it {
        acc = ctx.mk_and(p, acc);
    }
    acc
}

/// Project the `i`-th conjunct from `h : ⟦and φ_0 … φ_{k-1}⟧` (the right-nested
/// `And` of `props`), proving `props[i]`, via `i` `And.right` peels then (unless it
/// is the last operand) one `And.left`. `O(k)` — the polynomial replacement for
/// the `2^atoms` truth-table on `and_pos`. Reuses [`and_project`] (the `And.left`/
/// `And.right` primitive).
fn project_nth_conjunct(ctx: &mut ReconstructCtx, h: ExprId, props: &[ExprId], i: usize) -> ExprId {
    let mut cur = h;
    for j in 0..i {
        let a = props[j];
        let b = and_chain_prop_of(ctx, &props[j + 1..]);
        cur = and_project(ctx, a, b, cur, false); // take the right component
    }
    if i == props.len() - 1 {
        cur // the last operand is the innermost right component — no further proj
    } else {
        let a = props[i];
        let b = and_chain_prop_of(ctx, &props[i + 1..]);
        and_project(ctx, a, b, cur, true) // take the left component
    }
}

/// Rule-specific `O(k)` reconstruction of `and_pos`: `(cl (not (and φ…)) φ_i)`.
/// `em ⟦and φ…⟧`; on the positive branch project `⟦φ_i⟧` out of the conjunction and
/// `Or.inr`, on the negative branch `Or.inl`. Returns `Ok(None)` if the clause is
/// not this shape (caller falls back to the truth-table). The result is
/// `check_against`-gated, so a wrong term is rejected, never accepted.
fn try_and_pos(
    ctx: &mut ReconstructCtx,
    conclusion: &[AletheLit],
) -> Result<Option<ExprId>, ReconstructError> {
    let [l0, l1] = conclusion else {
        return Ok(None);
    };
    if !l0.negated || l1.negated {
        return Ok(None);
    }
    let AletheTerm::App(head, operands) = &l0.atom else {
        return Ok(None);
    };
    if head != "and" || operands.is_empty() {
        return Ok(None);
    }
    let phi_key = l1.atom.key();
    let Some(i) = operands.iter().position(|op| op.key() == phi_key) else {
        return Ok(None);
    };

    let _ = ctx.em_axiom();
    let operands = operands.clone();
    let operand_props: Vec<ExprId> = operands
        .iter()
        .map(|op| ctx.gate_term_to_prop(op))
        .collect();
    let g_prop = and_chain_prop_of(ctx, &operand_props);
    let phi_prop = operand_props[i];
    let not_g = ctx.mk_not(g_prop);
    let target = ctx.mk_or(not_g, phi_prop);

    let anon = ctx.kernel.anon();

    // minor_inl := fun (hG : ⟦G⟧) => Or.inr not_g phi_prop (project_i hG).
    let fvar_g = fresh_fvar_id(ctx);
    let hg = ctx.kernel.fvar(fvar_g);
    let proj = project_nth_conjunct(ctx, hg, &operand_props, i);
    let inl_body = or_inr(ctx, not_g, phi_prop, proj);
    let inl_body = ctx.kernel.abstract_fvars(inl_body, &[fvar_g]);
    let minor_inl = ctx.kernel.lam(anon, g_prop, inl_body, BinderInfo::Default);

    // minor_inr := fun (hnG : Not ⟦G⟧) => Or.inl not_g phi_prop hnG.
    let fvar_ng = fresh_fvar_id(ctx);
    let hng = ctx.kernel.fvar(fvar_ng);
    let inr_body = or_inl(ctx, not_g, phi_prop, hng);
    let inr_body = ctx.kernel.abstract_fvars(inr_body, &[fvar_ng]);
    let minor_inr = ctx.kernel.lam(anon, not_g, inr_body, BinderInfo::Default);

    // Or.rec.{0} ⟦G⟧ (Not ⟦G⟧) (fun _ => target) minor_inl minor_inr (em ⟦G⟧).
    let or_g = ctx.mk_or(g_prop, not_g);
    let motive = ctx.kernel.lam(anon, or_g, target, BinderInfo::Default);
    let em_name = ctx.em_axiom();
    let em = ctx.kernel.const_(em_name, vec![]);
    let em_g = ctx.kernel.app(em, g_prop);
    let z = ctx.kernel.level_zero();
    let rec = ctx.kernel.const_(ctx.prelude.or_rec, vec![z]);
    let e = ctx.kernel.app(rec, g_prop);
    let e = ctx.kernel.app(e, not_g);
    let e = ctx.kernel.app(e, motive);
    let e = ctx.kernel.app(e, minor_inl);
    let e = ctx.kernel.app(e, minor_inr);
    let proof = ctx.kernel.app(e, em_g);

    Ok(Some(check_against(ctx, "and_pos", proof, target)?))
}

/// Right-nested `And.intro` of `witnesses` (proofs of `props[i]`) into a proof of
/// `⟦and props⟧` — the inverse of [`project_nth_conjunct`].
fn and_intro_fold(ctx: &mut ReconstructCtx, props: &[ExprId], witnesses: &[ExprId]) -> ExprId {
    let n = props.len();
    let mut acc = witnesses[n - 1];
    for i in (0..n - 1).rev() {
        let a = props[i];
        let b = and_chain_prop_of(ctx, &props[i + 1..]);
        acc = and_intro(ctx, a, b, witnesses[i], acc);
    }
    acc
}

/// Recursive core of [`try_and_neg`]: case-split `em ⟦φ_j⟧` for each operand; on
/// the first false operand inject its negated literal, and when all hold build
/// `⟦and φ…⟧` by [`and_intro_fold`] and inject it at position 0. `target` is the
/// fixed clause `Prop`; `witnesses` accumulates the positive-operand fvars.
fn build_and_neg(
    ctx: &mut ReconstructCtx,
    clause: &[AletheLit],
    props: &[ExprId],
    j: usize,
    target: ExprId,
    witnesses: &mut Vec<ExprId>,
) -> ExprId {
    if j == props.len() {
        let g = and_intro_fold(ctx, props, witnesses);
        return inject_gate_lit(ctx, clause, 0, g);
    }
    let anon = ctx.kernel.anon();
    let p = props[j];
    let not_p = ctx.mk_not(p);

    // inl: φ_j holds — record the witness and recurse.
    let fv = fresh_fvar_id(ctx);
    let h = ctx.kernel.fvar(fv);
    witnesses.push(h);
    let body_inl = build_and_neg(ctx, clause, props, j + 1, target, witnesses);
    witnesses.pop();
    let body_inl = ctx.kernel.abstract_fvars(body_inl, &[fv]);
    let minor_inl = ctx.kernel.lam(anon, p, body_inl, BinderInfo::Default);

    // inr: ¬φ_j — inject the negated operand at clause position j+1.
    let fv2 = fresh_fvar_id(ctx);
    let hn = ctx.kernel.fvar(fv2);
    let inj = inject_gate_lit(ctx, clause, j + 1, hn);
    let body_inr = ctx.kernel.abstract_fvars(inj, &[fv2]);
    let minor_inr = ctx.kernel.lam(anon, not_p, body_inr, BinderInfo::Default);

    let or_p_notp = ctx.mk_or(p, not_p);
    let motive = ctx.kernel.lam(anon, or_p_notp, target, BinderInfo::Default);
    let em_name = ctx.em_axiom();
    let em = ctx.kernel.const_(em_name, vec![]);
    let em_p = ctx.kernel.app(em, p);
    let z = ctx.kernel.level_zero();
    let rec = ctx.kernel.const_(ctx.prelude.or_rec, vec![z]);
    let e = ctx.kernel.app(rec, p);
    let e = ctx.kernel.app(e, not_p);
    let e = ctx.kernel.app(e, motive);
    let e = ctx.kernel.app(e, minor_inl);
    let e = ctx.kernel.app(e, minor_inr);
    ctx.kernel.app(e, em_p)
}

/// Rule-specific `O(k)` reconstruction of `and_neg`:
/// `(cl (and φ…) (not φ_0) … (not φ_{k-1}))`. Nested `em` over the operands; the
/// first false operand discharges its negated literal, all-true builds the
/// conjunction. Returns `Ok(None)` for an unexpected shape (caller falls back).
fn try_and_neg(
    ctx: &mut ReconstructCtx,
    conclusion: &[AletheLit],
) -> Result<Option<ExprId>, ReconstructError> {
    let Some((l0, rest)) = conclusion.split_first() else {
        return Ok(None);
    };
    if l0.negated {
        return Ok(None);
    }
    let AletheTerm::App(head, operands) = &l0.atom else {
        return Ok(None);
    };
    if head != "and" || operands.len() != rest.len() || operands.is_empty() {
        return Ok(None);
    }
    // Each tail literal must be `¬φ_j` for the j-th operand (peel a `(not …)` atom
    // or a `negated` flag; either spelling denotes `Not ⟦φ_j⟧`).
    for (op, lit) in operands.iter().zip(rest) {
        let neg = normalize_lit_polarity(lit);
        if !neg.negated || neg.atom.key() != op.key() {
            return Ok(None);
        }
    }

    let _ = ctx.em_axiom();
    let operands = operands.clone();
    let conclusion = conclusion.to_vec();
    let props: Vec<ExprId> = operands
        .iter()
        .map(|op| ctx.gate_term_to_prop(op))
        .collect();
    let target = ctx.gate_clause_to_prop(&conclusion);
    let mut witnesses: Vec<ExprId> = Vec::new();
    let proof = build_and_neg(ctx, &conclusion, &props, 0, target, &mut witnesses);
    Ok(Some(check_against(ctx, "and_neg", proof, target)?))
}

/// Rule-specific `O(1)` reconstruction of `or_pos`: `(cl (not (or φ…)) φ_0 … φ_{k-1})`.
/// The clause tail `φ_0 ∨ … ∨ φ_{k-1}` is *exactly* `⟦or φ…⟧`, so no projection is
/// needed: `em ⟦G⟧`; on the positive branch the witness already proves the tail
/// (`Or.inr`), on the negative branch `Or.inl`. Returns `Ok(None)` for an
/// unexpected shape (caller falls back).
fn try_or_pos(
    ctx: &mut ReconstructCtx,
    conclusion: &[AletheLit],
) -> Result<Option<ExprId>, ReconstructError> {
    let Some((l0, tail)) = conclusion.split_first() else {
        return Ok(None);
    };
    if !l0.negated || tail.is_empty() {
        return Ok(None);
    }
    let AletheTerm::App(head, operands) = &l0.atom else {
        return Ok(None);
    };
    if head != "or" || operands.len() != tail.len() {
        return Ok(None);
    }
    // The tail must be the operands as positive literals, in order.
    for (op, lit) in operands.iter().zip(tail) {
        if lit.negated || lit.atom.key() != op.key() {
            return Ok(None);
        }
    }

    let _ = ctx.em_axiom();
    let conclusion = conclusion.to_vec();
    let tail_prop = ctx.gate_clause_to_prop(&conclusion[1..]); // ⟦G⟧ (= the or-chain)
    let not_g = ctx.mk_not(tail_prop);
    let target = ctx.gate_clause_to_prop(&conclusion); // Or(not_g, tail_prop)

    let anon = ctx.kernel.anon();
    // minor_inl := fun (hG : tail_prop) => Or.inr not_g tail_prop hG.
    let fv = fresh_fvar_id(ctx);
    let hg = ctx.kernel.fvar(fv);
    let inl_body = or_inr(ctx, not_g, tail_prop, hg);
    let inl_body = ctx.kernel.abstract_fvars(inl_body, &[fv]);
    let minor_inl = ctx
        .kernel
        .lam(anon, tail_prop, inl_body, BinderInfo::Default);
    // minor_inr := fun (hnG : Not tail_prop) => Or.inl not_g tail_prop hnG.
    let fv2 = fresh_fvar_id(ctx);
    let hng = ctx.kernel.fvar(fv2);
    let inr_body = or_inl(ctx, not_g, tail_prop, hng);
    let inr_body = ctx.kernel.abstract_fvars(inr_body, &[fv2]);
    let minor_inr = ctx.kernel.lam(anon, not_g, inr_body, BinderInfo::Default);

    let or_g = ctx.mk_or(tail_prop, not_g);
    let motive = ctx.kernel.lam(anon, or_g, target, BinderInfo::Default);
    let em_name = ctx.em_axiom();
    let em = ctx.kernel.const_(em_name, vec![]);
    let em_g = ctx.kernel.app(em, tail_prop);
    let z = ctx.kernel.level_zero();
    let rec = ctx.kernel.const_(ctx.prelude.or_rec, vec![z]);
    let e = ctx.kernel.app(rec, tail_prop);
    let e = ctx.kernel.app(e, not_g);
    let e = ctx.kernel.app(e, motive);
    let e = ctx.kernel.app(e, minor_inl);
    let e = ctx.kernel.app(e, minor_inr);
    let proof = ctx.kernel.app(e, em_g);

    Ok(Some(check_against(ctx, "or_pos", proof, target)?))
}

/// Rule-specific `O(k)` reconstruction of `or_neg`: `(cl (or φ…) (not φ_i))`.
/// `em ⟦φ_i⟧`; on the positive branch inject the witness into the or-chain `⟦G⟧`
/// at position `i` (`inject_gate_lit` over the operands-as-clause) and `Or.inl`, on
/// the negative branch `Or.inr`. Returns `Ok(None)` for an unexpected shape.
fn try_or_neg(
    ctx: &mut ReconstructCtx,
    conclusion: &[AletheLit],
) -> Result<Option<ExprId>, ReconstructError> {
    let [l0, l1] = conclusion else {
        return Ok(None);
    };
    if l0.negated {
        return Ok(None);
    }
    let neg = normalize_lit_polarity(l1);
    if !neg.negated {
        return Ok(None);
    }
    let AletheTerm::App(head, operands) = &l0.atom else {
        return Ok(None);
    };
    if head != "or" || operands.is_empty() {
        return Ok(None);
    }
    let Some(i) = operands.iter().position(|op| op.key() == neg.atom.key()) else {
        return Ok(None);
    };

    let _ = ctx.em_axiom();
    let operands = operands.clone();
    let conclusion = conclusion.to_vec();
    // The operands as a positive clause: its encoding is `⟦G⟧` (the or-chain).
    let operand_clause: Vec<AletheLit> = operands
        .iter()
        .map(|op| AletheLit {
            atom: op.clone(),
            negated: false,
        })
        .collect();
    let g_prop = ctx.gate_clause_to_prop(&operand_clause);
    let phi_prop = ctx.gate_term_to_prop(&operands[i]);
    let not_phi = ctx.mk_not(phi_prop);
    let target = ctx.gate_clause_to_prop(&conclusion); // Or(⟦G⟧, Not ⟦φ_i⟧)

    let anon = ctx.kernel.anon();
    // minor_inl := fun (h : ⟦φ_i⟧) => Or.inl ⟦G⟧ not_phi (inject_i h).
    let fv = fresh_fvar_id(ctx);
    let h = ctx.kernel.fvar(fv);
    let g_proof = inject_gate_lit(ctx, &operand_clause, i, h);
    let inl_body = or_inl(ctx, g_prop, not_phi, g_proof);
    let inl_body = ctx.kernel.abstract_fvars(inl_body, &[fv]);
    let minor_inl = ctx
        .kernel
        .lam(anon, phi_prop, inl_body, BinderInfo::Default);
    // minor_inr := fun (hn : Not ⟦φ_i⟧) => Or.inr ⟦G⟧ not_phi hn.
    let fv2 = fresh_fvar_id(ctx);
    let hn = ctx.kernel.fvar(fv2);
    let inr_body = or_inr(ctx, g_prop, not_phi, hn);
    let inr_body = ctx.kernel.abstract_fvars(inr_body, &[fv2]);
    let minor_inr = ctx.kernel.lam(anon, not_phi, inr_body, BinderInfo::Default);

    let or_phi = ctx.mk_or(phi_prop, not_phi);
    let motive = ctx.kernel.lam(anon, or_phi, target, BinderInfo::Default);
    let em_name = ctx.em_axiom();
    let em = ctx.kernel.const_(em_name, vec![]);
    let em_phi = ctx.kernel.app(em, phi_prop);
    let z = ctx.kernel.level_zero();
    let rec = ctx.kernel.const_(ctx.prelude.or_rec, vec![z]);
    let e = ctx.kernel.app(rec, phi_prop);
    let e = ctx.kernel.app(e, not_phi);
    let e = ctx.kernel.app(e, motive);
    let e = ctx.kernel.app(e, minor_inl);
    let e = ctx.kernel.app(e, minor_inr);
    let proof = ctx.kernel.app(e, em_phi);

    Ok(Some(check_against(ctx, "or_neg", proof, target)?))
}

/// Rule-specific `O(1)` reconstruction of the `equiv_*` / `xor_*` rules, whose gate
/// `(= a b)` (or `(xor a b) = Not Iff`) has exactly **two** operands `a, b`. Instead
/// of the `2^leaves` truth-table over the operands' bit leaves, case-split only over
/// `{a, b}` (the four `em ⟦a⟧ × em ⟦b⟧` cases) via the shared `prove_clause_by_cases`
/// engine — `prove_term_true/false` now treats `a, b` as opaque atoms. Polynomial
/// regardless of how large the operand gates are. Returns `Ok(None)` if no `=`/`xor`
/// gate literal is present (caller falls back).
fn try_equiv_xor(
    ctx: &mut ReconstructCtx,
    rule_name: &str,
    conclusion: &[AletheLit],
) -> Result<Option<ExprId>, ReconstructError> {
    let mut operands: Option<(AletheTerm, AletheTerm)> = None;
    for lit in conclusion {
        if let AletheTerm::App(head, args) = &lit.atom {
            if (head == "=" || head == "xor") && args.len() == 2 {
                operands = Some((args[0].clone(), args[1].clone()));
                break;
            }
        }
    }
    let Some((a, b)) = operands else {
        return Ok(None);
    };

    let _ = ctx.em_axiom();
    // Case-split atoms: the two operands, deduplicated by key. A **constant-valued**
    // operand (one with no free atoms, e.g. `false` or `(not false)` — common in
    // bit-blasted adders over constant operands) is NOT case-split: it is a fixed
    // truth value, so `prove_term` evaluates it at the leaf. Case-splitting it would
    // explore impossible worlds and falsely reject a valid clause.
    let mut atoms: Vec<(String, AletheTerm)> = Vec::new();
    for op in [a, b] {
        let mut leaves = Vec::new();
        collect_atoms(&op, &mut leaves);
        if leaves.is_empty() {
            continue; // constant-valued operand
        }
        let key = op.key();
        if !atoms.iter().any(|(k, _)| k == &key) {
            atoms.push((key, op));
        }
    }
    let target = ctx.gate_clause_to_prop(conclusion);
    let conclusion = conclusion.to_vec();
    let mut assignment = Assignment::new();
    let proof = prove_clause_by_cases(ctx, &atoms, 0, &mut assignment, &conclusion, target)?;
    Ok(Some(check_against(ctx, rule_name, proof, target)?))
}

/// Reconstruct a Tseitin **CNF-introduction** rule into a kernel-checked Lean
/// proof term of its conclusion clause's `Prop` encoding.
///
/// `rule_name` is the Alethe rule (`and_pos`/`and_neg`/`or_pos`/`or_neg`,
/// `equiv_pos1`/`equiv_pos2`/`equiv_neg1`/`equiv_neg2`,
/// `xor_pos1`/`xor_pos2`/`xor_neg1`/`xor_neg2`); `conclusion` is the rule's
/// conclusion clause. Each such clause is a propositional **tautology** over the
/// structured gate (`And`/`Or`/`Iff`/`Not`, with `xor` modeled as `Not Iff`) of
/// its operand atoms. The returned proof term is `infer`-checked and
/// [`Kernel::def_eq`]-compared to the clause's `gate_clause_to_prop`
/// encoding — the kernel is the gate.
///
/// Rules with a direct polynomial proof (`and_pos`) are handled rule-specifically;
/// the rest fall back to a classical case-split (via the context's `em`) over every
/// distinct operand atom, injecting the satisfied literal into the conclusion's
/// `Or` encoding in each leaf. A wrong conclusion makes the satisfied-literal
/// search fail or the kernel reject — never a wrong "checked".
///
/// # Errors
///
/// Returns [`ReconstructError::UnsupportedRule`] for a rule outside the
/// CNF-introduction set, [`ReconstructError::MalformedStep`] for a clause that is
/// not a tautology under the gate model (some truth assignment satisfies no
/// literal), and [`ReconstructError::KernelRejected`] when the kernel's `infer`
/// fails or the inferred proposition is not `def_eq` to the conclusion. It never
/// panics on malformed or out-of-scope input.
pub fn reconstruct_cnf_intro_rule(
    ctx: &mut ReconstructCtx,
    rule_name: &str,
    conclusion: &[AletheLit],
) -> Result<ExprId, ReconstructError> {
    match rule_name {
        "and_pos" | "and_neg" | "or_pos" | "or_neg" | "equiv_pos1" | "equiv_pos2"
        | "equiv_neg1" | "equiv_neg2" | "xor_pos1" | "xor_pos2" | "xor_neg1" | "xor_neg2" => {}
        other => {
            return Err(ReconstructError::UnsupportedRule {
                rule: other.to_owned(),
            });
        }
    }

    // Rule-specific polynomial proofs (replacing the `2^atoms` truth-table) where
    // available; fall back to `prove_clause_by_cases` for the rest.
    if rule_name == "and_pos" {
        if let Some(proof) = try_and_pos(ctx, conclusion)? {
            return Ok(proof);
        }
    }
    if rule_name == "and_neg" {
        if let Some(proof) = try_and_neg(ctx, conclusion)? {
            return Ok(proof);
        }
    }
    if rule_name == "or_pos" {
        if let Some(proof) = try_or_pos(ctx, conclusion)? {
            return Ok(proof);
        }
    }
    if rule_name == "or_neg" {
        if let Some(proof) = try_or_neg(ctx, conclusion)? {
            return Ok(proof);
        }
    }
    if matches!(
        rule_name,
        "equiv_pos1"
            | "equiv_pos2"
            | "equiv_neg1"
            | "equiv_neg2"
            | "xor_pos1"
            | "xor_pos2"
            | "xor_neg1"
            | "xor_neg2"
    ) {
        if let Some(proof) = try_equiv_xor(ctx, rule_name, conclusion)? {
            return Ok(proof);
        }
    }

    // Ensure `em` is available for the classical case-split.
    let _ = ctx.em_axiom();

    // Collect the distinct operand atoms (the case-split variables) in a stable
    // order (s-expression key order via the BTreeSet-like collection below).
    let mut atom_keys: Vec<(String, AletheTerm)> = Vec::new();
    for lit in conclusion {
        collect_atoms(&lit.atom, &mut atom_keys);
    }

    let target = ctx.gate_clause_to_prop(conclusion);
    let conclusion = conclusion.to_vec();

    // Recursively case-split on each atom; at the leaf, inject the satisfied lit.
    let mut assignment = Assignment::new();
    let proof = prove_clause_by_cases(ctx, &atom_keys, 0, &mut assignment, &conclusion, target)?;

    check_against(ctx, rule_name, proof, target)
}

/// Collect the distinct **operand atoms** of a gate term — the leaves that are
/// not Boolean connectives — keyed by s-expression, in first-seen order.
fn collect_atoms(term: &AletheTerm, out: &mut Vec<(String, AletheTerm)>) {
    match term {
        AletheTerm::App(head, args)
            if (head == "not" && args.len() == 1)
                || ((head == "and" || head == "or") && !args.is_empty())
                || ((head == "=" || head == "xor") && args.len() == 2) =>
        {
            for a in args {
                collect_atoms(a, out);
            }
        }
        // The Boolean literals are FIXED values, not free atoms — never case-split
        // them (doing so explores impossible worlds, e.g. `(not false) = false`, and
        // a real tautology then looks falsified). `prove_term_true/false` evaluate
        // them directly.
        AletheTerm::Const(s) if s == "true" || s == "false" => {}
        other => {
            let key = other.key();
            if !out.iter().any(|(k, _)| k == &key) {
                out.push((key, other.clone()));
            }
        }
    }
}

/// Case-split on `atoms[idx..]` via `em`, accumulating each atom's truth witness
/// in `assignment`; at the leaf (`idx == atoms.len()`) build the satisfied
/// literal's proof and inject it into the clause's `Or` encoding `target`.
fn prove_clause_by_cases(
    ctx: &mut ReconstructCtx,
    atoms: &[(String, AletheTerm)],
    idx: usize,
    assignment: &mut Assignment,
    conclusion: &[AletheLit],
    target: ExprId,
) -> Result<ExprId, ReconstructError> {
    if idx == atoms.len() {
        return prove_clause_leaf(ctx, conclusion, target, assignment);
    }

    let (key, atom_term) = atoms[idx].clone();
    let p = ctx.gate_term_to_prop(&atom_term);

    // `em p : Or p (Not p)`. Case-split with `Or.rec` into `target`.
    let em_name = ctx.em_axiom();
    let em = ctx.kernel.const_(em_name, vec![]);
    let em_p = ctx.kernel.app(em, p);

    let not_p = ctx.mk_not(p);
    let anon = ctx.kernel.anon();

    // minor_inl := fun (hp : p) => <recurse with key ↦ true>.
    let fvar_true = fresh_fvar_id(ctx);
    let hp = ctx.kernel.fvar(fvar_true);
    assignment.map.insert(key.clone(), (p, hp, true));
    let body_true = prove_clause_by_cases(ctx, atoms, idx + 1, assignment, conclusion, target)?;
    assignment.map.remove(&key);
    let body_true = ctx.kernel.abstract_fvars(body_true, &[fvar_true]);
    let minor_inl = ctx.kernel.lam(anon, p, body_true, BinderInfo::Default);

    // minor_inr := fun (hnp : Not p) => <recurse with key ↦ false>.
    let fvar_false = fresh_fvar_id(ctx);
    let hnp = ctx.kernel.fvar(fvar_false);
    assignment.map.insert(key.clone(), (p, hnp, false));
    let body_false = prove_clause_by_cases(ctx, atoms, idx + 1, assignment, conclusion, target)?;
    assignment.map.remove(&key);
    let body_false = ctx.kernel.abstract_fvars(body_false, &[fvar_false]);
    let minor_inr = ctx.kernel.lam(anon, not_p, body_false, BinderInfo::Default);

    // motive := fun (_ : Or p (Not p)) => target.
    let or_p_notp = ctx.mk_or(p, not_p);
    let motive = ctx.kernel.lam(anon, or_p_notp, target, BinderInfo::Default);

    // Or.rec.{0} p (Not p) motive minor_inl minor_inr (em p) : target.
    let z = ctx.kernel.level_zero();
    let rec = ctx.kernel.const_(ctx.prelude.or_rec, vec![z]);
    let e = ctx.kernel.app(rec, p);
    let e = ctx.kernel.app(e, not_p);
    let e = ctx.kernel.app(e, motive);
    let e = ctx.kernel.app(e, minor_inl);
    let e = ctx.kernel.app(e, minor_inr);
    Ok(ctx.kernel.app(e, em_p))
}

/// At a complete truth assignment, find a satisfied clause literal and inject its
/// proof into the right-nested `Or` encoding `target = gate_clause_to_prop(conclusion)`.
fn prove_clause_leaf(
    ctx: &mut ReconstructCtx,
    conclusion: &[AletheLit],
    target: ExprId,
    assignment: &Assignment,
) -> Result<ExprId, ReconstructError> {
    let _ = target;
    // Find the first literal satisfied under the assignment, with its proof.
    for (idx, lit) in conclusion.iter().enumerate() {
        if let Some(lit_proof) = prove_lit(ctx, lit, assignment)? {
            return Ok(inject_gate_lit(ctx, conclusion, idx, lit_proof));
        }
    }
    // No literal holds in this assignment ⇒ the clause is NOT a tautology.
    let clause_keys: Vec<String> = conclusion
        .iter()
        .map(|l| {
            let neg = if l.negated { "¬" } else { "" };
            format!("{neg}{}", l.atom.key())
        })
        .collect();
    let assign_keys: Vec<String> = assignment
        .map
        .iter()
        .map(|(k, &(_, _, v))| format!("{k}={v}"))
        .collect();
    Err(ReconstructError::MalformedStep {
        rule: "cnf_intro".to_owned(),
        detail: format!(
            "conclusion clause is not a tautology under the gate model; \
             clause = [{}] falsified by {{{}}}",
            clause_keys.join(", "),
            assign_keys.join(", ")
        ),
    })
}

/// Inject a proof `lit_proof : gate_lit_to_prop(conclusion[idx])` into the
/// right-nested `Or` encoding `target` at position `idx` via `Or.inl`/`Or.inr`.
fn inject_gate_lit(
    ctx: &mut ReconstructCtx,
    conclusion: &[AletheLit],
    idx: usize,
    lit_proof: ExprId,
) -> ExprId {
    let n = conclusion.len();
    debug_assert!(idx < n);
    let mut proof = lit_proof;
    for i in (0..=idx).rev() {
        if i == idx {
            if idx == n - 1 {
                // Last literal: the suffix is just `Enc(lit)`; nothing to wrap.
            } else {
                let a = ctx.gate_lit_to_prop(&conclusion[idx]);
                let b = ctx.gate_clause_to_prop(&conclusion[idx + 1..]);
                proof = or_inl(ctx, a, b, proof);
            }
        } else {
            let a = ctx.gate_lit_to_prop(&conclusion[i]);
            let b = ctx.gate_clause_to_prop(&conclusion[i + 1..]);
            proof = or_inr(ctx, a, b, proof);
        }
    }
    proof
}

/// Build a proof of a gate **literal** under the assignment, or `None` if the
/// literal is not satisfied. A positive literal `t` needs `⟦t⟧` (so `t` evaluates
/// true); a negated `(not t)` needs `Not ⟦t⟧` (so `t` evaluates false).
fn prove_lit(
    ctx: &mut ReconstructCtx,
    lit: &AletheLit,
    assignment: &Assignment,
) -> Result<Option<ExprId>, ReconstructError> {
    if lit.negated {
        prove_term_false(ctx, &lit.atom, assignment)
    } else {
        prove_term_true(ctx, &lit.atom, assignment)
    }
}

/// Build a proof of `⟦term⟧` (the structured gate Prop) under the assignment, or
/// `None` if `term` evaluates to false there. Recurses structurally over the
/// gate; atoms are looked up in the assignment.
#[allow(clippy::too_many_lines)]
fn prove_term_true(
    ctx: &mut ReconstructCtx,
    term: &AletheTerm,
    assignment: &Assignment,
) -> Result<Option<ExprId>, ReconstructError> {
    // If `term` itself is a case-split atom, use its witness directly rather than
    // recursing into its gate structure. For the leaf-atom truth-table this never
    // fires on a compound term (only leaves are atoms); it lets a coarser case-split
    // (e.g. over a predicate's two operands) treat those operands as opaque.
    if let Some(&(_, proof, val)) = assignment.map.get(&term.key()) {
        return Ok(val.then_some(proof));
    }
    // The Boolean literals: `true` is provable (`True.intro`), `false` is not.
    if let AletheTerm::Const(s) = term {
        if s == "true" {
            return Ok(Some(ctx.kernel.const_(ctx.prelude.true_intro, vec![])));
        }
        if s == "false" {
            return Ok(None);
        }
    }
    match term {
        // (not t) is true ⇔ t is false ⇒ a `Not ⟦t⟧` proof.
        AletheTerm::App(head, args) if head == "not" && args.len() == 1 => {
            prove_term_false(ctx, &args[0], assignment)
        }
        // (and t…) is true ⇔ every operand is true; fold `And.intro` right-nested.
        AletheTerm::App(head, args) if head == "and" && !args.is_empty() => {
            // Build the proof from the last operand inward. At each step `acc`
            // proves the And of the operands *after* index `i`; `And.intro` of the
            // operand at `i` extends it leftward.
            let n = args.len();
            let Some(mut acc) = prove_term_true(ctx, &args[n - 1], assignment)? else {
                return Ok(None);
            };
            for i in (0..n - 1).rev() {
                let Some(ht) = prove_term_true(ctx, &args[i], assignment)? else {
                    return Ok(None);
                };
                // acc : ⟦args[i+1..]⟧ ; ht : ⟦args[i]⟧ ⇒ And.intro a b ht acc.
                let a = ctx.gate_term_to_prop(&args[i]);
                let b = and_chain_prop(ctx, &args[i + 1..]);
                acc = and_intro(ctx, a, b, ht, acc);
            }
            Ok(Some(acc))
        }
        // (or t…) is true ⇔ some operand is true; inject with Or.inl/Or.inr.
        AletheTerm::App(head, args) if head == "or" && !args.is_empty() => {
            prove_or_true(ctx, args, assignment)
        }
        // (= a b) (boolean iff) is true ⇔ a, b have the SAME truth value.
        AletheTerm::App(head, args) if head == "=" && args.len() == 2 => {
            prove_iff_true(ctx, &args[0], &args[1], assignment)
        }
        // (xor a b) = Not (Iff a b) is true ⇔ a, b DIFFER ⇒ a `Not (Iff a b)` proof.
        AletheTerm::App(head, args) if head == "xor" && args.len() == 2 => {
            prove_iff_false(ctx, &args[0], &args[1], assignment)
        }
        // An atom: look it up.
        other => {
            let key = other.key();
            match assignment.map.get(&key) {
                Some(&(_, proof, true)) => Ok(Some(proof)),
                _ => Ok(None),
            }
        }
    }
}

/// Build a proof of `Not ⟦term⟧` under the assignment, or `None` if `term`
/// evaluates true there. Recurses structurally over the gate.
fn prove_term_false(
    ctx: &mut ReconstructCtx,
    term: &AletheTerm,
    assignment: &Assignment,
) -> Result<Option<ExprId>, ReconstructError> {
    // Symmetric to `prove_term_true`: a case-split atom uses its `Not`-witness
    // directly (stored for the `false` branch) instead of recursing into the gate.
    if let Some(&(_, proof, val)) = assignment.map.get(&term.key()) {
        return Ok((!val).then_some(proof));
    }
    // The Boolean literals: `false` is refutable (`Not False` = `id : False → False`),
    // `true` is not.
    if let AletheTerm::Const(s) = term {
        if s == "false" {
            let false_ = ctx.kernel.const_(ctx.prelude.false_, vec![]);
            let anon = ctx.kernel.anon();
            let body = ctx.kernel.bvar(0);
            return Ok(Some(ctx.kernel.lam(
                anon,
                false_,
                body,
                BinderInfo::Default,
            )));
        }
        if s == "true" {
            return Ok(None);
        }
    }
    match term {
        // Not (not t) ⇔ t is true. We have a proof `ht : ⟦t⟧`; build a proof of
        // `Not (Not ⟦t⟧)` = `(⟦t⟧ → False) → False` as `fun hnt => hnt ht`.
        AletheTerm::App(head, args) if head == "not" && args.len() == 1 => {
            let Some(ht) = prove_term_true(ctx, &args[0], assignment)? else {
                return Ok(None);
            };
            let inner = ctx.gate_term_to_prop(&args[0]);
            let not_inner = ctx.mk_not(inner);
            // fun (hnt : Not ⟦t⟧) => hnt ht : Not (Not ⟦t⟧).
            let anon = ctx.kernel.anon();
            let fv = fresh_fvar_id(ctx);
            let hnt = ctx.kernel.fvar(fv);
            let body = ctx.kernel.app(hnt, ht);
            let body = ctx.kernel.abstract_fvars(body, &[fv]);
            Ok(Some(ctx.kernel.lam(
                anon,
                not_inner,
                body,
                BinderInfo::Default,
            )))
        }
        // Not (and t…) ⇔ some operand is false. With `hnf : Not ⟦tᵢ⟧`, build
        // `fun (h : ⟦and⟧) => hnf (project tᵢ from h)`.
        AletheTerm::App(head, args) if head == "and" && !args.is_empty() => {
            prove_and_false(ctx, args, assignment)
        }
        // Not (or t…) ⇔ every operand is false. With each `hnf_i : Not ⟦tᵢ⟧`,
        // build `fun (h : ⟦or⟧) => Or.rec … h` discharging each branch.
        AletheTerm::App(head, args) if head == "or" && !args.is_empty() => {
            prove_or_false(ctx, args, assignment)
        }
        // Not (= a b) ⇔ a, b differ.
        AletheTerm::App(head, args) if head == "=" && args.len() == 2 => {
            prove_iff_false(ctx, &args[0], &args[1], assignment)
        }
        // Not (xor a b) = Not (Not (Iff a b)) ⇔ a, b agree ⇒ `Not (Not (Iff))`.
        AletheTerm::App(head, args) if head == "xor" && args.len() == 2 => {
            let Some(iff_proof) = prove_iff_true(ctx, &args[0], &args[1], assignment)? else {
                return Ok(None);
            };
            let a = ctx.gate_term_to_prop(&args[0]);
            let b = ctx.gate_term_to_prop(&args[1]);
            let iff = ctx.mk_iff(a, b);
            let not_iff = ctx.mk_not(iff);
            // fun (hn : Not (Iff a b)) => hn iff_proof : Not (Not (Iff a b)).
            let anon = ctx.kernel.anon();
            let fv = fresh_fvar_id(ctx);
            let hn = ctx.kernel.fvar(fv);
            let body = ctx.kernel.app(hn, iff_proof);
            let body = ctx.kernel.abstract_fvars(body, &[fv]);
            Ok(Some(ctx.kernel.lam(
                anon,
                not_iff,
                body,
                BinderInfo::Default,
            )))
        }
        // An atom: look it up for a `Not`-witness.
        other => {
            let key = other.key();
            match assignment.map.get(&key) {
                Some(&(_, proof, false)) => Ok(Some(proof)),
                _ => Ok(None),
            }
        }
    }
}

/// `And.intro a b ha hb : And a b`.
fn and_intro(ctx: &mut ReconstructCtx, a: ExprId, b: ExprId, ha: ExprId, hb: ExprId) -> ExprId {
    let intro = ctx.kernel.const_(ctx.prelude.and_intro, vec![]);
    let e = ctx.kernel.app(intro, a);
    let e = ctx.kernel.app(e, b);
    let e = ctx.kernel.app(e, ha);
    ctx.kernel.app(e, hb)
}

/// `And.rec`-project: from `h : And a b` produce a proof of the projection at
/// `select` (`true` = left operand `a`, `false` = right operand `b`).
fn and_project(
    ctx: &mut ReconstructCtx,
    a: ExprId,
    b: ExprId,
    h: ExprId,
    select_left: bool,
) -> ExprId {
    let anon = ctx.kernel.anon();
    let target = if select_left { a } else { b };
    // motive := fun (_ : And a b) => target.
    let and_ab = ctx.mk_and(a, b);
    let motive = ctx.kernel.lam(anon, and_ab, target, BinderInfo::Default);
    // minor := fun (ha : a) (hb : b) => (ha | hb).
    //   Under binders ha, hb: ha = BVar 1, hb = BVar 0.
    let chosen = if select_left {
        ctx.kernel.bvar(1)
    } else {
        ctx.kernel.bvar(0)
    };
    let inner = ctx.kernel.lam(anon, b, chosen, BinderInfo::Default);
    let minor = ctx.kernel.lam(anon, a, inner, BinderInfo::Default);
    // And.rec.{0} a b motive minor h : target.
    let z = ctx.kernel.level_zero();
    let rec = ctx.kernel.const_(ctx.prelude.and_rec, vec![z]);
    let e = ctx.kernel.app(rec, a);
    let e = ctx.kernel.app(e, b);
    let e = ctx.kernel.app(e, motive);
    let e = ctx.kernel.app(e, minor);
    ctx.kernel.app(e, h)
}

/// Build a proof of `Or ⟦t0⟧ (Or … ⟦tn⟧)` when some operand is true.
fn prove_or_true(
    ctx: &mut ReconstructCtx,
    args: &[AletheTerm],
    assignment: &Assignment,
) -> Result<Option<ExprId>, ReconstructError> {
    // Find the first true operand and inject; the Or is right-nested.
    let n = args.len();
    for (idx, t) in args.iter().enumerate() {
        if let Some(t_proof) = prove_term_true(ctx, t, assignment)? {
            // Inject `t_proof` at position `idx` into the right-nested Or of `args`.
            let mut proof = t_proof;
            for i in (0..=idx).rev() {
                if i == idx {
                    if idx == n - 1 {
                        // last operand: the suffix is `⟦t⟧`; nothing to wrap.
                    } else {
                        let a = ctx.gate_term_to_prop(&args[idx]);
                        let b = or_chain_prop(ctx, &args[idx + 1..]);
                        proof = or_inl(ctx, a, b, proof);
                    }
                } else {
                    let a = ctx.gate_term_to_prop(&args[i]);
                    let b = or_chain_prop(ctx, &args[i + 1..]);
                    proof = or_inr(ctx, a, b, proof);
                }
            }
            return Ok(Some(proof));
        }
    }
    Ok(None)
}

/// The `Prop` of the right-nested `Or` chain of a non-empty operand slice.
fn or_chain_prop(ctx: &mut ReconstructCtx, args: &[AletheTerm]) -> ExprId {
    let (last, rest) = args.split_last().expect("non-empty Or chain");
    let mut acc = ctx.gate_term_to_prop(last);
    for t in rest.iter().rev() {
        let head = ctx.gate_term_to_prop(t);
        acc = ctx.mk_or(head, acc);
    }
    acc
}

/// Build a proof of `Not (Or ⟦t0⟧ …)` when every operand is false. We have
/// `hnf_i : Not ⟦tᵢ⟧` for each; `fun (h : Or …) => Or.rec … h` discharges each
/// branch into `False` by applying the matching `hnf`.
fn prove_or_false(
    ctx: &mut ReconstructCtx,
    args: &[AletheTerm],
    assignment: &Assignment,
) -> Result<Option<ExprId>, ReconstructError> {
    // Collect a `Not ⟦tᵢ⟧` proof for every operand; bail if any is true.
    let mut neg_proofs: Vec<ExprId> = Vec::with_capacity(args.len());
    for t in args {
        let Some(p) = prove_term_false(ctx, t, assignment)? else {
            return Ok(None);
        };
        neg_proofs.push(p);
    }
    // Build `fun (h : ⟦or⟧) => elim(h) : False`, then it is the `Not ⟦or⟧` proof.
    let or_prop = or_chain_prop(ctx, args);
    let anon = ctx.kernel.anon();
    let fv = fresh_fvar_id(ctx);
    let h = ctx.kernel.fvar(fv);
    let false_const = ctx.kernel.const_(ctx.prelude.false_, vec![]);
    let body = or_chain_to_false(ctx, args, h, &neg_proofs, false_const);
    let body = ctx.kernel.abstract_fvars(body, &[fv]);
    Ok(Some(ctx.kernel.lam(
        anon,
        or_prop,
        body,
        BinderInfo::Default,
    )))
}

/// Eliminate `h : Or ⟦args[0]⟧ (Or … )` into `False`, given a `Not ⟦argsᵢ⟧` proof
/// for each operand. Recurses over the right-nested `Or` via `Or.rec`.
fn or_chain_to_false(
    ctx: &mut ReconstructCtx,
    args: &[AletheTerm],
    h: ExprId,
    neg_proofs: &[ExprId],
    false_const: ExprId,
) -> ExprId {
    match args {
        [_t] => {
            // h : ⟦t⟧; neg_proofs[0] : Not ⟦t⟧ = ⟦t⟧ → False.
            ctx.kernel.app(neg_proofs[0], h)
        }
        [t0, rest @ ..] => {
            let anon = ctx.kernel.anon();
            let a = ctx.gate_term_to_prop(t0);
            let b = or_chain_prop(ctx, rest);
            // motive := fun (_ : Or a b) => False.
            let or_ab = ctx.mk_or(a, b);
            let motive = ctx
                .kernel
                .lam(anon, or_ab, false_const, BinderInfo::Default);
            // minor_inl := fun (h0 : a) => neg_proofs[0] h0.
            let fv0 = fresh_fvar_id(ctx);
            let h0 = ctx.kernel.fvar(fv0);
            let body0 = ctx.kernel.app(neg_proofs[0], h0);
            let body0 = ctx.kernel.abstract_fvars(body0, &[fv0]);
            let minor_inl = ctx.kernel.lam(anon, a, body0, BinderInfo::Default);
            // minor_inr := fun (hr : b) => <recurse on rest>.
            let fvr = fresh_fvar_id(ctx);
            let hr = ctx.kernel.fvar(fvr);
            let body_r = or_chain_to_false(ctx, rest, hr, &neg_proofs[1..], false_const);
            let body_r = ctx.kernel.abstract_fvars(body_r, &[fvr]);
            let minor_inr = ctx.kernel.lam(anon, b, body_r, BinderInfo::Default);
            // Or.rec.{0} a b motive minor_inl minor_inr h : False.
            let z = ctx.kernel.level_zero();
            let rec = ctx.kernel.const_(ctx.prelude.or_rec, vec![z]);
            let e = ctx.kernel.app(rec, a);
            let e = ctx.kernel.app(e, b);
            let e = ctx.kernel.app(e, motive);
            let e = ctx.kernel.app(e, minor_inl);
            let e = ctx.kernel.app(e, minor_inr);
            ctx.kernel.app(e, h)
        }
        [] => false_const,
    }
}

/// Build a proof of `Not (And ⟦args[0]⟧ …)` when some operand is false. With
/// `hnf : Not ⟦tᵢ⟧`, the proof is `fun (h : ⟦and⟧) => hnf (project tᵢ from h)`.
fn prove_and_false(
    ctx: &mut ReconstructCtx,
    args: &[AletheTerm],
    assignment: &Assignment,
) -> Result<Option<ExprId>, ReconstructError> {
    // Find a false operand; project it out of the And and feed it to its `Not`.
    let n = args.len();
    let mut false_idx = None;
    for (idx, t) in args.iter().enumerate() {
        if prove_term_false(ctx, t, assignment)?.is_some() {
            false_idx = Some(idx);
            break;
        }
    }
    let Some(idx) = false_idx else {
        return Ok(None);
    };
    let hnf = prove_term_false(ctx, &args[idx], assignment)?.expect("operand was just shown false");

    // and_prop = And a0 (And a1 (… an)); project operand `idx` out of `h`.
    let and_prop = and_chain_prop(ctx, args);
    let anon = ctx.kernel.anon();
    let fv = fresh_fvar_id(ctx);
    let h = ctx.kernel.fvar(fv);
    // Walk down the right-nested And to reach operand `idx`: take `.right` `idx`
    // times to reach the And of `args[idx..]`, then `.left` (unless it is the
    // last operand, where the residual IS `args[idx]`).
    let mut cur = h;
    for i in 0..idx {
        let a = ctx.gate_term_to_prop(&args[i]);
        let b = and_chain_prop(ctx, &args[i + 1..]);
        cur = and_project(ctx, a, b, cur, false); // take right
    }
    let proj = if idx == n - 1 {
        cur
    } else {
        let a = ctx.gate_term_to_prop(&args[idx]);
        let b = and_chain_prop(ctx, &args[idx + 1..]);
        and_project(ctx, a, b, cur, true) // take left
    };
    let body = ctx.kernel.app(hnf, proj);
    let body = ctx.kernel.abstract_fvars(body, &[fv]);
    Ok(Some(ctx.kernel.lam(
        anon,
        and_prop,
        body,
        BinderInfo::Default,
    )))
}

/// The `Prop` of the right-nested `And` chain of a non-empty operand slice.
fn and_chain_prop(ctx: &mut ReconstructCtx, args: &[AletheTerm]) -> ExprId {
    let (last, rest) = args.split_last().expect("non-empty And chain");
    let mut acc = ctx.gate_term_to_prop(last);
    for t in rest.iter().rev() {
        let head = ctx.gate_term_to_prop(t);
        acc = ctx.mk_and(head, acc);
    }
    acc
}

/// Build a proof of `Iff ⟦a⟧ ⟦b⟧` when `a`, `b` have the same truth value, else
/// `None`. `Iff.intro a b mp mpr` with both directions; the direction not taken
/// by the live branch is discharged ex-falso (it is never reached, but must
/// type-check), so we build it from the operand witnesses directly.
fn prove_iff_true(
    ctx: &mut ReconstructCtx,
    a_t: &AletheTerm,
    b_t: &AletheTerm,
    assignment: &Assignment,
) -> Result<Option<ExprId>, ReconstructError> {
    let a_true = prove_term_true(ctx, a_t, assignment)?;
    let b_true = prove_term_true(ctx, b_t, assignment)?;
    let a = ctx.gate_term_to_prop(a_t);
    let b = ctx.gate_term_to_prop(b_t);
    let anon = ctx.kernel.anon();

    match (a_true, b_true) {
        // Both true: mp := fun (_ : a) => hb; mpr := fun (_ : b) => ha.
        (Some(ha), Some(hb)) => {
            let mp = ctx.kernel.lam(anon, a, hb, BinderInfo::Default);
            let mpr = ctx.kernel.lam(anon, b, ha, BinderInfo::Default);
            Ok(Some(iff_intro(ctx, a, b, mp, mpr)))
        }
        // Both false: mp := fun (ha : a) => absurd; mpr := fun (hb : b) => absurd.
        (None, None) => {
            let hna = prove_term_false(ctx, a_t, assignment)?.expect("a is false");
            let hnb = prove_term_false(ctx, b_t, assignment)?.expect("b is false");
            // mp : a → b := fun (ha : a) => False.rec (fun _ => b) (hna ha).
            let fv = fresh_fvar_id(ctx);
            let ha = ctx.kernel.fvar(fv);
            let false_app = ctx.kernel.app(hna, ha);
            let ex = ex_falso(ctx, b, false_app);
            let mp_body = ctx.kernel.abstract_fvars(ex, &[fv]);
            let mp = ctx.kernel.lam(anon, a, mp_body, BinderInfo::Default);
            // mpr : b → a := fun (hb : b) => False.rec (fun _ => a) (hnb hb).
            let fv2 = fresh_fvar_id(ctx);
            let hb = ctx.kernel.fvar(fv2);
            let false_app2 = ctx.kernel.app(hnb, hb);
            let ex2 = ex_falso(ctx, a, false_app2);
            let mpr_body = ctx.kernel.abstract_fvars(ex2, &[fv2]);
            let mpr = ctx.kernel.lam(anon, b, mpr_body, BinderInfo::Default);
            Ok(Some(iff_intro(ctx, a, b, mp, mpr)))
        }
        // Differ: not an Iff.
        _ => Ok(None),
    }
}

/// Build a proof of `Not (Iff ⟦a⟧ ⟦b⟧)` when `a`, `b` differ, else `None`. With
/// (say) `ha : a`, `hnb : Not b`: `fun (hiff : Iff a b) => hnb (hiff.mp ha)`.
fn prove_iff_false(
    ctx: &mut ReconstructCtx,
    a_t: &AletheTerm,
    b_t: &AletheTerm,
    assignment: &Assignment,
) -> Result<Option<ExprId>, ReconstructError> {
    let a_true = prove_term_true(ctx, a_t, assignment)?;
    let b_true = prove_term_true(ctx, b_t, assignment)?;
    let a = ctx.gate_term_to_prop(a_t);
    let b = ctx.gate_term_to_prop(b_t);
    let iff = ctx.mk_iff(a, b);
    let anon = ctx.kernel.anon();

    // We need exactly one of a,b true and the other false.
    let (mp_dir, hpos, hneg) = match (a_true, b_true) {
        (Some(ha), None) => {
            // a true, b false: hiff.mp ha : b, contradict with hnb.
            let hnb = prove_term_false(ctx, b_t, assignment)?.expect("b is false");
            (true, ha, hnb)
        }
        (None, Some(hb)) => {
            // a false, b true: hiff.mpr hb : a, contradict with hna.
            let hna = prove_term_false(ctx, a_t, assignment)?.expect("a is false");
            (false, hb, hna)
        }
        _ => return Ok(None),
    };

    // fun (hiff : Iff a b) => hneg ((Iff.rec … hiff) hpos) : False.
    let fv = fresh_fvar_id(ctx);
    let hiff = ctx.kernel.fvar(fv);
    // Extract the chosen direction from hiff via Iff.rec.
    let dir = iff_project(ctx, a, b, hiff, mp_dir);
    // Apply the direction to hpos to get the other side, then contradict.
    let other = ctx.kernel.app(dir, hpos);
    let body = ctx.kernel.app(hneg, other);
    let body = ctx.kernel.abstract_fvars(body, &[fv]);
    Ok(Some(ctx.kernel.lam(anon, iff, body, BinderInfo::Default)))
}

/// `Iff.intro a b mp mpr : Iff a b`.
fn iff_intro(ctx: &mut ReconstructCtx, a: ExprId, b: ExprId, mp: ExprId, mpr: ExprId) -> ExprId {
    let intro = ctx.kernel.const_(ctx.prelude.iff_intro, vec![]);
    let e = ctx.kernel.app(intro, a);
    let e = ctx.kernel.app(e, b);
    let e = ctx.kernel.app(e, mp);
    ctx.kernel.app(e, mpr)
}

/// `Iff.rec`-project the `mp : a → b` (`select_mp = true`) or `mpr : b → a`
/// (`false`) direction out of `h : Iff a b`.
fn iff_project(
    ctx: &mut ReconstructCtx,
    a: ExprId,
    b: ExprId,
    h: ExprId,
    select_mp: bool,
) -> ExprId {
    let anon = ctx.kernel.anon();
    // The projection's type: `a → b` (mp) or `b → a` (mpr).
    let (dom, cod) = if select_mp { (a, b) } else { (b, a) };
    let arrow = ctx.kernel.pi(anon, dom, cod, BinderInfo::Default);
    // motive := fun (_ : Iff a b) => arrow.
    let iff_ab = ctx.mk_iff(a, b);
    let motive = ctx.kernel.lam(anon, iff_ab, arrow, BinderInfo::Default);
    // minor := fun (mp : a → b) (mpr : b → a) => (mp | mpr).
    //   Under binders mp, mpr: mp = BVar 1, mpr = BVar 0.
    let chosen = if select_mp {
        ctx.kernel.bvar(1)
    } else {
        ctx.kernel.bvar(0)
    };
    // mpr : b → a (inner binder).
    let mpr_ty = ctx.kernel.pi(anon, b, a, BinderInfo::Default);
    let inner = ctx.kernel.lam(anon, mpr_ty, chosen, BinderInfo::Default);
    // mp : a → b (outer binder).
    let mp_ty = ctx.kernel.pi(anon, a, b, BinderInfo::Default);
    let minor = ctx.kernel.lam(anon, mp_ty, inner, BinderInfo::Default);
    // Iff.rec.{0} a b motive minor h : arrow.
    let z = ctx.kernel.level_zero();
    let rec = ctx.kernel.const_(ctx.prelude.iff_rec, vec![z]);
    let e = ctx.kernel.app(rec, a);
    let e = ctx.kernel.app(e, b);
    let e = ctx.kernel.app(e, motive);
    let e = ctx.kernel.app(e, minor);
    ctx.kernel.app(e, h)
}

// ===========================================================================
// Bit-blast reconstruction (P3.7 slice 5) — the BITWISE QF_BV fragment.
//
// This is the bottom layer of the QF_BV proof: the `bitblast_*` steps that
// connect a bit-vector predicate to its bit-level Boolean form, plus the
// `cong`/`trans`/`equiv1`/`equiv2` plumbing the emitter threads them with. It
// reconstructs the BITWISE fragment only — `bitblast_var`, `bitblast_const`,
// `bitblast_not`, `bitblast_and`, `bitblast_or`, `bitblast_xor`, and
// `bitblast_equal`. Anything with a carry chain (`bitblast_add`/`_mult`/`_neg`),
// a shift, div/rem, or a structural reshaping (`extract`/`concat`/`sign_extend`)
// is explicitly REJECTED here (no panic) — those are later slices.
//
// ## The faithful bit model
//
// A width-`n` bit-vector term is modeled bit-by-bit, each bit a Lean `Prop`:
//
// - a **variable** `x`'s bit `i` is the opaque Prop atom keyed by the
//   projection `((_ @bit_of i) x)` (shared with the clausal `prop_atoms`);
// - a **constant** `#b…`'s bit `i` is the prelude's `True`/`False`;
// - `bvnot a` bit `i` is `Not (bit_i a)`;
// - `bvand a b` bit `i` is `And (bit_i a) (bit_i b)` (pointwise);
// - `bvor  a b` bit `i` is `Or  (bit_i a) (bit_i b)`;
// - `bvxor a b` bit `i` is `Not (Iff (bit_i a) (bit_i b))` (xor = ¬iff, the same
//   modeling choice the Tseitin/CNF-intro layer makes).
//
// So the bitwise operators are POINTWISE on bits — and the `bitblast_<op>`
// gadget the emitter writes (`(and (@bit_of i a) (@bit_of i b))`, …) is, under
// this model, the **same** structured Prop as `bv_bit` produces. The bitblast
// equalities are therefore reflexive: `bit_i(lhs) ↔ gadget_i` is `Iff.refl`.
//
// ## What a `bitblast_*` step reconstructs to
//
// Each step's conclusion is a unit clause `(= lhs rhs)`. `rhs` is either a
// `(@bbterm b0 … b_{n-1})` (a term op) or a single Boolean `B` (the predicate
// `bitblast_equal`). The reconstruction proves the **bit-iff conjunction**
//
//     ⋀_i ( bv_bit(lhs, i)  ↔  ⟦b_i⟧ )
//
// (for `bitblast_equal`, the single iff `⟦B⟧ ↔ ⟦B⟧`, i.e. the per-bit-AND form),
// each conjunct an `Iff.refl`-style identity, `And.intro`-folded for `n > 1`. The
// kernel `infer`s the assembled term and `def_eq`-checks it against that
// conjunction — the trusted gate. A wrong gadget bit makes some conjunct's two
// sides differ, the reflexive proof fails to type, and the kernel rejects.
// ===========================================================================

impl ReconstructCtx {
    /// Build a reflexive `Iff p p` proof: `Iff.intro p p (fun h => h) (fun h => h)`.
    fn mk_iff_refl(&mut self, p: ExprId) -> ExprId {
        let anon = self.kernel.anon();
        // id := fun (h : p) => h.
        let h = self.kernel.bvar(0);
        let id = self.kernel.lam(anon, p, h, BinderInfo::Default);
        iff_intro(self, p, p, id, id)
    }
}

/// The Lean `Prop` for bit `i` of a **bitwise** bit-vector term `term` under the
/// faithful bit model. Variables → opaque `((_ @bit_of i) x)` atom Props;
/// constants → `True`/`False`; `bvnot`/`bvand`/`bvor`/`bvxor`/`bvxnor` → pointwise
/// `Not`/`And`/`Or`/`Not (Iff …)`/`Iff` of the operand bits.
///
/// # Errors
///
/// Returns [`ReconstructError::UnsupportedTerm`] for any operator outside the
/// bitwise + `extract` + `bvadd`/`bvneg`/`bvmul` fragment (shifts, div/rem,
/// `concat`/`sign_extend`, n-ary `bvadd`/`bvmul`, …), a non-bit-vector shape, or
/// an out-of-range bit of a known-width constant. `extract` (bit `i` → bit
/// `lo + i`) and binary `bvadd`/`bvneg`/`bvmul` (carry chains) are supported.
#[allow(clippy::too_many_lines)] // a flat per-operator bit dispatch; clearer inline
fn bv_bit(
    ctx: &mut ReconstructCtx,
    term: &AletheTerm,
    i: usize,
) -> Result<ExprId, ReconstructError> {
    match term {
        // A bit-vector constant `#b…` (MSB-first binary literal): bit `i` is
        // `True`/`False`. A bare symbol (variable): bit `i` is the opaque
        // projection atom `((_ @bit_of i) x)`.
        AletheTerm::Const(symbol) => {
            if let Some(bits) = parse_bv_literal(symbol) {
                // `bits` is LSB-first; out-of-range index is malformed.
                let bit = *bits
                    .get(i)
                    .ok_or_else(|| ReconstructError::UnsupportedTerm {
                        term: format!("bit {i} of constant {symbol}"),
                    })?;
                let name = if bit {
                    ctx.prelude.true_
                } else {
                    ctx.prelude.false_
                };
                Ok(ctx.kernel.const_(name, vec![]))
            } else {
                let proj = bit_of_atom(symbol, i);
                Ok(ctx.gate_term_to_prop(&proj))
            }
        }
        AletheTerm::App(head, args) => match (head.as_str(), args.as_slice()) {
            // A `(@bbterm b0 … b_{n-1})` operand: bit `i` is its `i`-th bit Prop
            // directly (resolving `@bit_of i (@bbterm …)` to `bs[i]`). This is how
            // the emitter feeds an already-bit-blasted child into the next operator.
            ("@bbterm", bits) => {
                let bit = bits
                    .get(i)
                    .ok_or_else(|| ReconstructError::UnsupportedTerm {
                        term: format!("bit {i} out of range of `{}`", term.key()),
                    })?;
                Ok(gadget_bit_to_prop(ctx, bit))
            }
            ("bvnot", [a]) => {
                let ai = bv_bit(ctx, a, i)?;
                Ok(ctx.mk_not(ai))
            }
            ("bvand", [a, b]) => {
                let ai = bv_bit(ctx, a, i)?;
                let bi = bv_bit(ctx, b, i)?;
                Ok(ctx.mk_and(ai, bi))
            }
            ("bvor", [a, b]) => {
                let ai = bv_bit(ctx, a, i)?;
                let bi = bv_bit(ctx, b, i)?;
                Ok(ctx.mk_or(ai, bi))
            }
            ("bvxor", [a, b]) => {
                let ai = bv_bit(ctx, a, i)?;
                let bi = bv_bit(ctx, b, i)?;
                let iff = ctx.mk_iff(ai, bi);
                Ok(ctx.mk_not(iff))
            }
            // Bitwise XNOR (binary): bit `i` is `(= a_i b_i)`, i.e. `a_i ↔ b_i`,
            // matching the emitter's `bitblast_xnor`. Pointwise, width-free.
            ("bvxnor", [a, b]) => {
                let ai = bv_bit(ctx, a, i)?;
                let bi = bv_bit(ctx, b, i)?;
                Ok(ctx.mk_iff(ai, bi))
            }
            // Ripple-carry adder (binary). Bit `i` of `(bvadd a b)` is
            // `a_i ⊕ b_i ⊕ carry_i`, needing only bits `0..=i` (no operand width).
            // We rebuild the exact emitter bit *term* (`ripple_carry_bits`) and run
            // it through the same `gate_term_to_prop` the gadget side uses, so the
            // per-bit iff is reflexive by construction (constant-bit/`false`-seed
            // rendering can never diverge — both sides take the identical path).
            ("bvadd", [a, b]) => {
                let bit_term = ripple_carry_bit_term(a, b, i);
                Ok(ctx.gate_term_to_prop(&bit_term))
            }
            // Two's-complement negate: `-x = (not x) + 1`, a width-free ripple
            // carry (carry-in `true`). Same reflexive build-and-gate as `bvadd`.
            ("bvneg", [x]) => {
                let bit_term = neg_bit_term(x, i);
                Ok(ctx.gate_term_to_prop(&bit_term))
            }
            // Two's-complement subtract: by the SMT-LIB definition `bvsub a b` =
            // `bvadd a (bvneg b)`, so bit `i` is the ripple-carry sum of `a` and
            // `(bvneg b)`. This is the FAITHFUL bit model of `bvsub` (the same
            // definitional reduction Carcara's `bv_poly_simp` validates at the term
            // level); modeling it here makes the Route-2 `bvsub`-rewrite proof's
            // projection `((_ @bit_of i) (bvsub a b))` resolve to exactly the
            // `bvadd a (bvneg b)` gadget bit the emitter wrote — so the bit-definition
            // is reflexive (`Iff.refl`) and the certified `False` is over the ORIGINAL
            // `bvsub` assertion, not a pre-lowered one.
            ("bvsub", [a, b]) => {
                let neg_b = AletheTerm::App("bvneg".to_owned(), vec![b.clone()]);
                let bit_term = ripple_carry_bit_term(a, &neg_b, i);
                Ok(ctx.gate_term_to_prop(&bit_term))
            }
            // Shift-add multiplier (binary). Result bit `i` is `res[i][i]` of the
            // emitter's triangle, width-free. Same reflexive build-and-gate.
            //
            // The inlined (un-shared) result term grows ~4.5x per bit, so a wide
            // multiplier explodes memory. Guard with a node-count budget: beyond it
            // we return a clean `UnsupportedTerm` rather than OOM. (A shared/`let`
            // encoding — emitter and reconstruction both — is the real fix; see the
            // findings note.)
            ("bvmul", [a, b]) => {
                let nodes = mult_bit_node_count(i);
                if nodes > MULT_BIT_NODE_BUDGET {
                    return Err(ReconstructError::UnsupportedTerm {
                        term: format!(
                            "bvmul bit {i} reconstructs to ~{nodes} inlined nodes \
                             (> {MULT_BIT_NODE_BUDGET}); needs a shared encoding"
                        ),
                    });
                }
                let bit_term = mult_bit_term(a, b, i);
                Ok(ctx.gate_term_to_prop(&bit_term))
            }
            // `(concat a b)` (a high, b low): result bit `i` is `b_i` for
            // `i < width(b)`, else `a_{i - width(b)}` — the emitter emits the low
            // operand's bits first. Handled here (not only in `lhs_bit_prop`) so a
            // `concat` nested inside a projection gadget resolves structurally.
            ("concat", [hi, lo]) => {
                let width_lo =
                    alethe_bv_width(ctx, lo).ok_or_else(|| ReconstructError::UnsupportedTerm {
                        term: format!("concat low-operand width unknown `{}`", term.key()),
                    })?;
                if i < width_lo {
                    bv_bit(ctx, lo, i)
                } else {
                    bv_bit(ctx, hi, i - width_lo)
                }
            }
            // `(bvcomp x y)`: a 1-bit result, its only bit the per-bit-equality AND.
            ("bvcomp", [x, y]) if i == 0 => {
                let width = alethe_bv_width(ctx, x)
                    .or_else(|| alethe_bv_width(ctx, y))
                    .ok_or_else(|| ReconstructError::UnsupportedTerm {
                        term: format!("bvcomp operand width unknown `{}`", term.key()),
                    })?;
                if width == 0 {
                    return Err(ReconstructError::MalformedStep {
                        rule: "bitblast_comp".to_owned(),
                        detail: "zero-width bvcomp operand".to_owned(),
                    });
                }
                let bit_term = comp_bit_term(x, y, width);
                Ok(ctx.gate_term_to_prop(&bit_term))
            }
            // **Constant** left/right shifts (`bvshl`/`bvlshr`/`bvashr` by a
            // bit-vector **literal** amount). These route bit `i` to *exactly* the
            // bit the `lower_const_shift` rewrite (`axeyum_rewrite`) collapses them
            // to — `bvshl k` → `(concat (extract a (w-1-k) 0) (bv0 k))` etc. — so
            // proving `(= shift concat)` per-bit is reflexive by construction and the
            // previously-TRUSTED lowering identity becomes kernel-checked (the gate
            // rejects any divergent routing). A *variable* shift amount stays out of
            // fragment (no literal `k`): falls through to the catch-all below.
            ("bvshl" | "bvlshr" | "bvashr", [a, amt]) => const_shift_bit(ctx, head, a, amt, i),
            _ => Err(ReconstructError::UnsupportedTerm {
                term: format!("non-bitwise bit-blast operand `{}`", term.key()),
            }),
        },
        // `((_ extract hi lo) x)`: bit `i` of the result is bit `lo + i` of `x`
        // (pure bit routing — no carry/structural logic), matching the emitter's
        // `bitblast_extract` (bits `lo..=hi` of `x`, LSB-first). Reflexive against
        // the gadget bit by construction; the kernel gate catches any divergence.
        AletheTerm::Indexed { op, indices, args } if op == "extract" => {
            let [hi, lo] = indices.as_slice() else {
                return Err(ReconstructError::UnsupportedTerm {
                    term: format!("extract needs two indices `{}`", term.key()),
                });
            };
            let [x] = args.as_slice() else {
                return Err(ReconstructError::UnsupportedTerm {
                    term: format!("extract needs one operand `{}`", term.key()),
                });
            };
            let lo = usize::try_from(*lo).map_err(|_| ReconstructError::UnsupportedTerm {
                term: format!("extract low index out of range `{}`", term.key()),
            })?;
            let hi = usize::try_from(*hi).map_err(|_| ReconstructError::UnsupportedTerm {
                term: format!("extract high index out of range `{}`", term.key()),
            })?;
            if hi < lo || i > hi - lo {
                return Err(ReconstructError::UnsupportedTerm {
                    term: format!("bit {i} out of range of extract `{}`", term.key()),
                });
            }
            bv_bit(ctx, x, lo + i)
        }
        // `((_ sign_extend by) x)`: bit `i` is `x_i` for `i < width(x)`, else the
        // sign bit `x_{width(x)-1}`. Handled here so a `sign_extend` nested inside a
        // projection gadget resolves structurally (the top-level case stays in
        // `lhs_bit_prop`, which already knows `result_width`).
        AletheTerm::Indexed { op, indices, args } if op == "sign_extend" => {
            let [by] = indices.as_slice() else {
                return Err(ReconstructError::UnsupportedTerm {
                    term: format!("sign_extend needs one index `{}`", term.key()),
                });
            };
            let [x] = args.as_slice() else {
                return Err(ReconstructError::UnsupportedTerm {
                    term: format!("sign_extend needs one operand `{}`", term.key()),
                });
            };
            let _ = by;
            let width_x =
                alethe_bv_width(ctx, x).ok_or_else(|| ReconstructError::UnsupportedTerm {
                    term: format!("sign_extend operand width unknown `{}`", term.key()),
                })?;
            if width_x == 0 {
                return Err(ReconstructError::MalformedStep {
                    rule: "bitblast_sign_extend".to_owned(),
                    detail: "zero-width sign_extend operand".to_owned(),
                });
            }
            let src = if i < width_x { i } else { width_x - 1 };
            bv_bit(ctx, x, src)
        }
        AletheTerm::Indexed { .. } => Err(ReconstructError::UnsupportedTerm {
            term: format!(
                "indexed operand outside the bitwise + extract fragment `{}`",
                term.key()
            ),
        }),
    }
}

/// The bit width of an Alethe bit-vector **term**, recovering it structurally so a
/// nested compound operand (in the projection-based gadget) can be bit-routed:
///
/// - `@bbterm b…` / `#b…` literal: the bit count, directly;
/// - a bare symbol: the width recorded by its `bitblast_var`/`bitblast_const` step
///   (via [`ReconstructCtx::bv_widths`]);
/// - `bvnot`/`bvand`/`bvor`/`bvxor`/`bvxnor`/`bvadd`/`bvneg`/`bvmul`: operand-0's
///   width (width-preserving ops);
/// - `((_ extract hi lo) x)`: `hi - lo + 1`;
/// - `((_ sign_extend by) x)`: `width(x) + by`;
/// - `(concat hi lo)`: `width(hi) + width(lo)`;
/// - `(bvcomp _ _)`: 1.
///
/// Returns [`None`] for an unrecognized / undeclared shape.
fn alethe_bv_width(ctx: &ReconstructCtx, term: &AletheTerm) -> Option<usize> {
    match term {
        AletheTerm::App(head, args) if head == "@bbterm" => Some(args.len()),
        AletheTerm::Const(name) => parse_bv_literal(name)
            .map_or_else(|| ctx.bv_widths.get(name).copied(), |b| Some(b.len())),
        AletheTerm::App(head, args) => match (head.as_str(), args.as_slice()) {
            // Width-preserving ops: operand-0's width.
            (
                "bvnot" | "bvand" | "bvor" | "bvxor" | "bvxnor" | "bvadd" | "bvmul" | "bvneg",
                [a, ..],
            ) => alethe_bv_width(ctx, a),
            ("bvcomp", [_, _]) => Some(1),
            ("concat", [hi, lo]) => Some(alethe_bv_width(ctx, hi)? + alethe_bv_width(ctx, lo)?),
            _ => None,
        },
        AletheTerm::Indexed { op, indices, args } if op == "extract" => {
            let [hi, lo] = indices.as_slice() else {
                return None;
            };
            let hi = usize::try_from(*hi).ok()?;
            let lo = usize::try_from(*lo).ok()?;
            (hi >= lo).then(|| hi - lo + 1)
        }
        AletheTerm::Indexed { op, indices, args } if op == "sign_extend" => {
            let [by] = indices.as_slice() else {
                return None;
            };
            let [x] = args.as_slice() else {
                return None;
            };
            let by = usize::try_from(*by).ok()?;
            Some(alethe_bv_width(ctx, x)? + by)
        }
        AletheTerm::Indexed { .. } => None,
    }
}

/// Whether a `((_ @bit_of i) operand)` projection should be resolved through the
/// faithful bit model [`bv_bit`] (rather than kept as an opaque atom).
///
/// - A **compound** bit-vector term (`@bbterm`, any `bv…`/`concat` application, or an
///   `extract`/`sign_extend`) → resolve, so the projection agrees structurally with
///   the LHS expansion in the projection-based emission.
/// - A `#b…` **literal** → resolve, so `((_ @bit_of i) #b…)` (which the emitter's
///   `build_term_vec` projects for a constant operand) becomes the constant `True`/
///   `False` bit, matching the LHS constant model.
/// - A **bare symbol** → do NOT resolve: `bv_bit` models a symbol's bit as the same
///   opaque `@bit_of` atom, so resolving would recurse; keeping it opaque is correct.
fn bit_of_operand_resolves(operand: &AletheTerm) -> bool {
    match operand {
        AletheTerm::Const(name) => parse_bv_literal(name).is_some(),
        AletheTerm::App(..) | AletheTerm::Indexed { .. } => true,
    }
}

/// The bit-projection atom `((_ @bit_of i) name)` as an [`AletheTerm`], matching
/// the emitter's spelling exactly so its opaque Prop key coincides.
fn bit_of_atom(name: &str, i: usize) -> AletheTerm {
    AletheTerm::Indexed {
        op: "@bit_of".to_owned(),
        indices: vec![i128::try_from(i).expect("bit index fits i128")],
        args: vec![AletheTerm::Const(name.to_owned())],
    }
}

/// Bit `j` of a bit-blast operand *as an [`AletheTerm`]*, mirroring the emitter's
/// `build_term_vec`: a `(@bbterm b…)` exposes its `j`-th bit directly, anything
/// else is the projection `((_ @bit_of j) operand)`.
fn operand_bit_term(operand: &AletheTerm, j: usize) -> AletheTerm {
    if let AletheTerm::App(head, args) = operand {
        if head == "@bbterm" {
            if let Some(bit) = args.get(j) {
                return bit.clone();
            }
        }
    }
    // A binary-literal constant `#b<MSB…LSB>`: bit `j` (LSB-first) is its actual
    // Boolean value, matching how the emitter bit-blasts a constant operand (bool
    // literals in the `@bbterm`), NOT an opaque `@bit_of` projection.
    if let AletheTerm::Const(lit) = operand {
        if let Some(bits) = lit.strip_prefix("#b") {
            let n = bits.len();
            if j < n {
                let is_one = bits.as_bytes()[n - 1 - j] == b'1';
                return AletheTerm::Const(if is_one { "true" } else { "false" }.to_owned());
            }
        }
    }
    AletheTerm::Indexed {
        op: "@bit_of".to_owned(),
        indices: vec![i128::try_from(j).expect("bit index fits i128")],
        args: vec![operand.clone()],
    }
}

/// Bit `i` of `(bvadd x y)` as an [`AletheTerm`], transcribing the emitter's
/// `ripple_carry_bits` verbatim (`carry_0 = false`;
/// `carry_k = (or (and x_{k-1} y_{k-1}) (and (xor x_{k-1} y_{k-1}) carry_{k-1}))`;
/// `bit_i = (xor (xor x_i y_i) carry_i)`). Building the term and gating it keeps
/// reconstruction reflexive with the gadget bit on both the structure and the
/// constant/`false` leaf rendering.
fn ripple_carry_bit_term(x: &AletheTerm, y: &AletheTerm, i: usize) -> AletheTerm {
    let app = |head: &str, args: Vec<AletheTerm>| AletheTerm::App(head.to_owned(), args);
    let mut carry = AletheTerm::Const("false".to_owned());
    for k in 1..=i {
        let xk = operand_bit_term(x, k - 1);
        let yk = operand_bit_term(y, k - 1);
        let and_xy = app("and", vec![xk.clone(), yk.clone()]);
        let xor_xy = app("xor", vec![xk, yk]);
        let and_carry = app("and", vec![xor_xy, carry]);
        carry = app("or", vec![and_xy, and_carry]);
    }
    let xi = operand_bit_term(x, i);
    let yi = operand_bit_term(y, i);
    let sum = app("xor", vec![xi, yi]);
    app("xor", vec![sum, carry])
}

/// Bit `i` of `(bvneg x)` as an [`AletheTerm`], transcribing the emitter's
/// `neg_step` verbatim: the ripple-carry adder of `(not x)` and `0` with carry-in
/// `true` (`c_0 = true`;
/// `c_k = (or (and (not x_{k-1}) false) (and (xor (not x_{k-1}) false) c_{k-1}))`;
/// `bit_i = (xor (xor (not x_i) false) c_i)`). Width-free (bits `0..=i` only) and
/// gated through `gate_term_to_prop` for reflexivity, like [`ripple_carry_bit_term`].
fn neg_bit_term(x: &AletheTerm, i: usize) -> AletheTerm {
    let app = |head: &str, args: Vec<AletheTerm>| AletheTerm::App(head.to_owned(), args);
    let not_bit = |j: usize| app("not", vec![operand_bit_term(x, j)]);
    let false_ = || AletheTerm::Const("false".to_owned());
    let mut carry = AletheTerm::Const("true".to_owned());
    for k in 1..=i {
        let nx = not_bit(k - 1);
        let and_false = app("and", vec![nx.clone(), false_()]);
        let xor_false = app("xor", vec![nx, false_()]);
        let and_carry = app("and", vec![xor_false, carry]);
        carry = app("or", vec![and_false, and_carry]);
    }
    let sum = app("xor", vec![not_bit(i), false_()]);
    app("xor", vec![sum, carry])
}

/// Bit `i` of `(bvmul x y)` as an [`AletheTerm`], transcribing the emitter's
/// `shift_add_multiplier_bits`. The multiplier result satisfies
/// `res[j][i] = res[i][i]` for every `j > i`, so result bit `i` is `res[i][i]` —
/// computable from rounds `0..=i` alone (running the emitter's triangle at
/// `size = i + 1`), hence width-free like the adders. Gated through
/// `gate_term_to_prop` for reflexivity with the gadget bit.
/// Node-count budget for an inlined `bvmul` result bit. Beyond this the un-shared
/// term (and the kernel `Expr`/`def_eq` over it) blows memory; ~width 7 is the
/// last bit under budget (width-8 bit-7 is ~41 k nodes). Reconstruction returns a
/// clean error past this; the durable fix is a shared/`let` encoding.
const MULT_BIT_NODE_BUDGET: u128 = 20_000;

/// Node count of `mult_bit_term(_, _, i)` *without building the term*, via the
/// same `shift_add_multiplier` recurrence — used to guard against the exponential
/// blowup before allocating. Mirrors the term shapes (`and`/`or`/`xor` = 1 + two
/// operands, `false` = 1, `and(y,x)` shift leaf = 3).
#[allow(clippy::needless_range_loop)] // the shift-add recurrence reads clearer with explicit j/k indices
fn mult_bit_node_count(i: usize) -> u128 {
    let size = i + 1;
    let shift = |j: usize, k: usize| -> u128 { if j <= k { 3 } else { 1 } };
    let mut res = vec![vec![0u128; size]; size];
    for k in 0..size {
        res[0][k] = shift(0, k);
    }
    for j in 1..size {
        let mut carry = vec![0u128; size];
        carry[0] = 1;
        for k in 1..size {
            carry[k] = if j < k {
                let r = res[j - 1][k - 1];
                let s = shift(j, k - 1);
                1 + (1 + r + s) + (1 + (1 + r + s) + carry[k - 1])
            } else {
                1
            };
        }
        for k in 0..size {
            res[j][k] = if k == 0 {
                shift(0, 0)
            } else if j > k {
                res[k][k]
            } else {
                1 + (1 + res[j - 1][k] + shift(j, k)) + carry[k]
            };
        }
    }
    res[size - 1][size - 1]
}

fn mult_bit_term(x: &AletheTerm, y: &AletheTerm, i: usize) -> AletheTerm {
    let size = i + 1;
    let app = |head: &str, args: Vec<AletheTerm>| AletheTerm::App(head.to_owned(), args);
    let false_ = || AletheTerm::Const("false".to_owned());
    // shift[j][k] = (and y_j x_{k-j}) for j <= k, else false.
    let shift: Vec<Vec<AletheTerm>> = (0..size)
        .map(|j| {
            (0..size)
                .map(|k| {
                    if j <= k {
                        app(
                            "and",
                            vec![operand_bit_term(y, j), operand_bit_term(x, k - j)],
                        )
                    } else {
                        false_()
                    }
                })
                .collect()
        })
        .collect();
    let mut res: Vec<Vec<AletheTerm>> = vec![(0..size).map(|k| shift[0][k].clone()).collect()];
    for j in 1..size {
        let mut carry_j = vec![false_()];
        for k in 1..size {
            let c = if j < k {
                app(
                    "or",
                    vec![
                        app(
                            "and",
                            vec![res[j - 1][k - 1].clone(), shift[j][k - 1].clone()],
                        ),
                        app(
                            "and",
                            vec![
                                app(
                                    "xor",
                                    vec![res[j - 1][k - 1].clone(), shift[j][k - 1].clone()],
                                ),
                                carry_j[k - 1].clone(),
                            ],
                        ),
                    ],
                )
            } else {
                false_()
            };
            carry_j.push(c);
        }
        let res_j: Vec<AletheTerm> = (0..size)
            .map(|k| {
                if k == 0 {
                    shift[0][0].clone()
                } else if j > k {
                    res[k][k].clone()
                } else {
                    app(
                        "xor",
                        vec![
                            app("xor", vec![res[j - 1][k].clone(), shift[j][k].clone()]),
                            carry_j[k].clone(),
                        ],
                    )
                }
            })
            .collect();
        res.push(res_j);
    }
    res[size - 1][size - 1].clone()
}

/// Parse an SMT-LIB `#b…` binary bit-vector literal into its LSB-first bit
/// values, or [`None`] if `symbol` is not such a literal (e.g. a variable name).
fn parse_bv_literal(symbol: &str) -> Option<Vec<bool>> {
    let rest = symbol.strip_prefix("#b")?;
    if rest.is_empty() || !rest.bytes().all(|c| c == b'0' || c == b'1') {
        return None;
    }
    // `#b` is MSB-first; reverse to LSB-first.
    Some(rest.bytes().rev().map(|c| c == b'1').collect())
}

/// The numeric value of a `#b…` bit-vector literal as a `u128`, or [`None`] if
/// `symbol` is not a literal or its width exceeds 128 bits. Used to read a
/// **constant shift amount** `k` (the only shift case reconstructed).
fn bv_literal_value(symbol: &str) -> Option<u128> {
    let bits = parse_bv_literal(symbol)?; // LSB-first
    if bits.len() > 128 {
        return None;
    }
    let mut value: u128 = 0;
    for (i, &b) in bits.iter().enumerate() {
        if b {
            value |= 1u128 << i;
        }
    }
    Some(value)
}

/// Bit `i` of a **constant** shift `(<op> a #b…)` (`op` ∈ `bvshl`/`bvlshr`/`bvashr`),
/// routed to exactly the source bit the `lower_const_shift` rewrite produces. With
/// operand width `w` and amount `k`:
///
/// - `bvshl`  (`a << k`): bit `i` is `False` for `i < k`, else `a_{i-k}`.
/// - `bvlshr` (`a >>ᵤ k`): bit `i` is `a_{i+k}` for `i+k < w`, else `False`.
/// - `bvashr` (`a >>ₛ k`): bit `i` is `a_{i+k}` for `i+k < w`, else the sign `a_{w-1}`.
///
/// The `k = 0` (identity) and `k ≥ w` (all-zero / all-sign) edges fall out of these
/// formulas directly. A non-literal amount yields [`ReconstructError::UnsupportedTerm`]
/// (a *variable* shift is out of fragment — not a missing rule, the term-model gap).
fn const_shift_bit(
    ctx: &mut ReconstructCtx,
    op: &str,
    a: &AletheTerm,
    amt: &AletheTerm,
    i: usize,
) -> Result<ExprId, ReconstructError> {
    let AletheTerm::Const(amt_sym) = amt else {
        return Err(ReconstructError::UnsupportedTerm {
            term: format!("non-constant {op} amount"),
        });
    };
    let k = bv_literal_value(amt_sym).ok_or_else(|| ReconstructError::UnsupportedTerm {
        term: format!("non-literal {op} amount `{amt_sym}`"),
    })?;
    let width = alethe_bv_width(ctx, a).ok_or_else(|| ReconstructError::UnsupportedTerm {
        term: format!("{op} operand width unknown"),
    })?;
    let width_u128 = u128::try_from(width).map_err(|_| ReconstructError::UnsupportedTerm {
        term: format!("{op} operand width too large"),
    })?;
    let i_u128 = u128::try_from(i).map_err(|_| ReconstructError::UnsupportedTerm {
        term: format!("{op} bit index too large"),
    })?;
    match op {
        "bvshl" => {
            if i_u128 < k {
                Ok(ctx.kernel.const_(ctx.prelude.false_, vec![]))
            } else {
                // `i - k < width` because `i < width` and `k ≥ 0`; the index fits `usize`.
                let src = i - usize::try_from(k).expect("k < i < width fits usize");
                bv_bit(ctx, a, src)
            }
        }
        "bvlshr" | "bvashr" => {
            if i_u128 + k < width_u128 {
                let src = i + usize::try_from(k).expect("i + k < width fits usize");
                bv_bit(ctx, a, src)
            } else if op == "bvashr" {
                bv_bit(ctx, a, width - 1) // sign bit
            } else {
                Ok(ctx.kernel.const_(ctx.prelude.false_, vec![]))
            }
        }
        other => Err(ReconstructError::UnsupportedTerm {
            term: format!("unexpected shift op `{other}`"),
        }),
    }
}

/// Reconstruct one **bitwise** `bitblast_*` step into a kernel-checked proof term
/// of its bit-iff conjunction.
///
/// `rule` is the bitblast rule (a term op concluding `(= lhs (@bbterm b…))`, or a
/// predicate — `bitblast_equal`/`bitblast_ult`/`bitblast_slt` — concluding
/// `(= <pred> B)` with `B` a single Boolean). The reconstructed term has type
///
/// - term op: `⋀_i ( bv_bit(lhs, i) ↔ ⟦b_i⟧ )` — one reflexive `Iff` per bit;
/// - predicate: `⟦B⟧ ↔ ⟦B⟧` (the reflexive iff of the bit-level form `B`).
///
/// Each conjunct is reflexive because `bv_bit(lhs, i)` is, by construction, the
/// same structured Prop as the gadget bit `⟦b_i⟧`. The kernel `infer`s the term
/// and `def_eq`-checks it against the stated conjunction.
///
/// # Errors
///
/// Returns [`ReconstructError::UnsupportedRule`] for a bitblast rule outside the
/// bitwise + `extract`/`sign_extend`/`concat` + `add`/`neg`/`mult` +
/// `ult`/`slt`/`comp` fragment (shifts, div/rem, …),
/// [`ReconstructError::MalformedStep`] for a conclusion that is
/// not the expected `(= lhs rhs)` shape, [`ReconstructError::UnsupportedTerm`] for
/// a non-bitwise operand, and [`ReconstructError::KernelRejected`] at the gate.
pub fn reconstruct_bitblast_step(
    ctx: &mut ReconstructCtx,
    rule: &str,
    conclusion: &[AletheLit],
) -> Result<ExprId, ReconstructError> {
    // The bitwise fragment, `extract` (bit-routing), and the carry-chain
    // arithmetic `bitblast_add` (binary) / `bitblast_neg` / `bitblast_mult`
    // (binary); reject the remaining shift/structural rules cleanly. (`add`/`mult`
    // over >2 operands surface as `UnsupportedTerm` from `bv_bit`.)
    match rule {
        "bitblast_var"
        | "bitblast_const"
        | "bitblast_not"
        | "bitblast_and"
        | "bitblast_or"
        | "bitblast_xor"
        | "bitblast_xnor"
        | "bitblast_extract"
        | "bitblast_sign_extend"
        | "bitblast_concat"
        | "bitblast_comp"
        | "bitblast_add"
        | "bitblast_neg"
        | "bitblast_mult"
        | "bitblast_equal"
        | "bitblast_ult"
        | "bitblast_slt" => {}
        other => {
            return Err(ReconstructError::UnsupportedRule {
                rule: format!(
                    "{other} (only the bitwise + extract + add/neg/mult bit-blast fragment is \
                     reconstructed)"
                ),
            });
        }
    }

    let (lhs, rhs) = bitblast_conclusion_sides(rule, conclusion)?;

    let (target, proof) = if matches!(rule, "bitblast_equal" | "bitblast_ult" | "bitblast_slt") {
        // `(= <pred> B)`: a bit-vector predicate (`=`/`bvult`/`bvslt`) whose
        // bit-level form `B` is a single Boolean (the per-bit-AND for `=`, the
        // unsigned/signed less-than ladder for `bvult`/`bvslt`). Reconstruct the
        // reflexive `⟦B⟧ ↔ ⟦B⟧`; the predicate's lhs connects to `B` via the bridge
        // in the end-to-end flow, exactly as for `bitblast_equal`.
        let b_prop = ctx.gate_term_to_prop(rhs);
        let iff = ctx.mk_iff(b_prop, b_prop);
        (iff, ctx.mk_iff_refl(b_prop))
    } else {
        // A term op `(= lhs (@bbterm b0 … b_{n-1}))`: prove the per-bit iff
        // conjunction `⋀_i ( bv_bit(lhs, i) ↔ ⟦b_i⟧ )`.
        let bits = bbterm_bits(rhs).ok_or_else(|| ReconstructError::MalformedStep {
            rule: rule.to_owned(),
            detail: "term-op conclusion rhs is not a `(@bbterm …)`".to_owned(),
        })?;
        if bits.is_empty() {
            return Err(ReconstructError::MalformedStep {
                rule: rule.to_owned(),
                detail: "empty `@bbterm` (zero-width bit-vector)".to_owned(),
            });
        }
        // Record a freshly bit-blasted leaf's width so structural consumers
        // (`concat`) can recover operand widths (bottom-up order: the leaf step
        // precedes its consumer's step).
        if matches!(rule, "bitblast_var" | "bitblast_const") {
            if let AletheTerm::Const(name) = lhs {
                ctx.bv_widths.insert(name.clone(), bits.len());
            }
        }
        // Build, per bit, `Iff (bv_bit lhs i) ⟦b_i⟧` and its reflexive proof; the
        // two sides coincide as Props, so the reflexive `Iff` type-checks. Fold
        // right with `And.intro` into the conjunction.
        let n = bits.len();
        let mut target = bit_iff_prop(ctx, lhs, &bits[n - 1], n - 1, n)?;
        let mut proof = bit_iff_refl(ctx, lhs, &bits[n - 1], n - 1, n)?;
        for i in (0..n - 1).rev() {
            let head_prop = bit_iff_prop(ctx, lhs, &bits[i], i, n)?;
            let head_proof = bit_iff_refl(ctx, lhs, &bits[i], i, n)?;
            proof = and_intro(ctx, head_prop, target, head_proof, proof);
            target = ctx.mk_and(head_prop, target);
        }
        (target, proof)
    };

    check_against(ctx, rule, proof, target)
}

/// Certify the **constant-shift → concat lowering identity** as a Lean-kernel-checked
/// theorem, turning the previously-TRUSTED `lower_const_shift` rewrite into an
/// externally-checked one.
///
/// Given a constant shift `shift = (<op> a #b…)` (`op` ∈ `bvshl`/`bvlshr`/`bvashr`,
/// the amount a bit-vector **literal**) and the `rhs` term `lower_const_shift`
/// collapses it to — `(concat (extract a (w-1-k) 0) (bv0 k))` for `bvshl`, the
/// `lshr`/`ashr` analogues, or the `k = 0` / `k ≥ w` edge forms — this proves the
/// **per-bit equality conjunction**
///
/// > `⋀_{i<width} ( bv_bit(shift, i) ↔ bv_bit(rhs, i) )`
///
/// i.e. *each bit of the shift is definitionally the corresponding bit of the
/// lowered concat*. Both sides route through the faithful `bv_bit` model; when the
/// lowering is correct they are the **same** `Prop`, so each conjunct is `Iff.refl`
/// and the `infer`/`def_eq` gate accepts. A **wrong** `rhs` (e.g. the wrong `k`, or
/// a swapped operand) makes some bit's two sides differ — the reflexive proof then
/// fails to `infer` to the stated conjunction and the kernel **rejects**. So the
/// check has teeth: it can never accept an unsound lowering.
///
/// `operand_width` is `a`'s bit width `w` (a bare-symbol operand carries no width in
/// the Alethe term); it is recorded in the context so the symbol's projection bits
/// route on both sides. This certifies **constant** shifts only — variable shifts and
/// division remain out of scope (a term-representation gap, not a missing rule).
///
/// # Errors
///
/// [`ReconstructError::UnsupportedTerm`] if `shift` is not a constant shift of a
/// bare-symbol operand, [`ReconstructError::MalformedStep`] for a zero width, and
/// [`ReconstructError::KernelRejected`] at the `infer`/`def_eq` gate (the soundness
/// boundary — a wrong lowering surfaces here as a rejection, never an accept).
pub fn reconstruct_const_shift_lowering(
    ctx: &mut ReconstructCtx,
    shift: &AletheTerm,
    rhs: &AletheTerm,
    operand_width: usize,
) -> Result<ExprId, ReconstructError> {
    if operand_width == 0 {
        return Err(ReconstructError::MalformedStep {
            rule: "const_shift_lowering".to_owned(),
            detail: "zero operand width".to_owned(),
        });
    }
    // Register the bare-symbol operand's width so `bv_bit`/`alethe_bv_width` can
    // route its projection bits on both sides.
    let AletheTerm::App(op, args) = shift else {
        return Err(ReconstructError::UnsupportedTerm {
            term: format!("not a shift application `{}`", shift.key()),
        });
    };
    let ("bvshl" | "bvlshr" | "bvashr", [a, _amt]) = (op.as_str(), args.as_slice()) else {
        return Err(ReconstructError::UnsupportedTerm {
            term: format!("not a constant `bvshl`/`bvlshr`/`bvashr` `{}`", shift.key()),
        });
    };
    if let AletheTerm::Const(name) = a {
        if parse_bv_literal(name).is_none() {
            ctx.bv_widths.insert(name.clone(), operand_width);
        }
    }

    // Build `⋀_i ( bv_bit(shift, i) ↔ bv_bit(rhs, i) )` and its reflexive proof,
    // folding right with `And.intro`. Each conjunct's two sides are the SAME `Prop`
    // exactly when the lowering is correct, so `mk_iff_refl` type-checks — the gate
    // rejects otherwise.
    let bit_iff = |ctx: &mut ReconstructCtx, i: usize| -> Result<ExprId, ReconstructError> {
        let l = bv_bit(ctx, shift, i)?;
        let r = bv_bit(ctx, rhs, i)?;
        Ok(ctx.mk_iff(l, r))
    };
    let last = operand_width - 1;
    let mut target = bit_iff(ctx, last)?;
    let mut proof = {
        let l = bv_bit(ctx, shift, last)?;
        ctx.mk_iff_refl(l)
    };
    for i in (0..last).rev() {
        let head_prop = bit_iff(ctx, i)?;
        let head_proof = {
            let l = bv_bit(ctx, shift, i)?;
            ctx.mk_iff_refl(l)
        };
        proof = and_intro(ctx, head_prop, target, head_proof, proof);
        target = ctx.mk_and(head_prop, target);
    }
    check_against(ctx, "const_shift_lowering", proof, target)
}

/// Certify the constant-shift lowering identity (see [`reconstruct_const_shift_lowering`])
/// **and render it as a self-contained Lean 4 module** an independent `lean` binary
/// can re-check.
///
/// Returns the `prelude`-mode source of `theorem <LEAN_MODULE_THEOREM> : <goal> :=
/// <proof>` (the per-bit equality conjunction) plus its `#print axioms` audit; a
/// faithful proof must report **no** `sorryAx`. A successful return means the
/// lowering identity was kernel-checked **and** rendered to externally-checkable
/// Lean — never a wrong identity.
///
/// # Errors
///
/// Same as [`reconstruct_const_shift_lowering`].
pub fn prove_const_shift_lowering_to_lean_module(
    shift: &AletheTerm,
    rhs: &AletheTerm,
    operand_width: usize,
) -> Result<String, ReconstructError> {
    let mut ctx = ReconstructCtx::new();
    let proof = reconstruct_const_shift_lowering(&mut ctx, shift, rhs, operand_width)?;
    let goal = ctx
        .kernel
        .infer(proof)
        .map_err(|e| ReconstructError::KernelRejected {
            rule: "const_shift_lowering".to_owned(),
            detail: format!("infer failed: {e:?}"),
        })?;
    Ok(ctx
        .kernel
        .render_lean_module(LEAN_MODULE_THEOREM, goal, proof))
}

/// Translate a `@bbterm` **gadget bit** into its `Prop`, agreeing with [`bv_bit`]
/// on the bit model: the Boolean literals `true`/`false` map to the prelude's
/// `True`/`False` (not an opaque atom), while bit projections and Boolean
/// connectives go through [`ReconstructCtx::gate_term_to_prop`] structurally.
fn gadget_bit_to_prop(ctx: &mut ReconstructCtx, bit: &AletheTerm) -> ExprId {
    match bit {
        AletheTerm::Const(s) if s == "true" => ctx.kernel.const_(ctx.prelude.true_, vec![]),
        AletheTerm::Const(s) if s == "false" => ctx.kernel.const_(ctx.prelude.false_, vec![]),
        other => ctx.gate_term_to_prop(other),
    }
}

/// The `Prop` for bit `i` of a term-op `lhs`. Routes through [`bv_bit`], except
/// for the width-needing top-level ops: `sign_extend` (operand width recovered as
/// `result_width - by`), `concat` (low-operand width via [`bv_operand_width`]), and
/// `bvcomp` (operand width via [`bv_operand_width`]). These appear only at the top
/// of their own step, never nested, so the width is known exactly here.
fn lhs_bit_prop(
    ctx: &mut ReconstructCtx,
    lhs: &AletheTerm,
    i: usize,
    result_width: usize,
) -> Result<ExprId, ReconstructError> {
    if let AletheTerm::Indexed { op, indices, args } = lhs {
        if op == "sign_extend" {
            // `((_ sign_extend by) x)`: result width = width(x) + by, so
            // width(x) = result_width - by. Bit `i` is `x_i` for `i < width(x)`,
            // else the sign bit `x_{width(x)-1}`. Matches the emitter
            // (`build_term_vec(x, width)` then `by` copies of the last bit).
            let [by] = indices.as_slice() else {
                return Err(ReconstructError::UnsupportedTerm {
                    term: format!("sign_extend needs one index `{}`", lhs.key()),
                });
            };
            let [x] = args.as_slice() else {
                return Err(ReconstructError::UnsupportedTerm {
                    term: format!("sign_extend needs one operand `{}`", lhs.key()),
                });
            };
            let by = usize::try_from(*by).map_err(|_| ReconstructError::UnsupportedTerm {
                term: format!("sign_extend amount out of range `{}`", lhs.key()),
            })?;
            let width_x =
                result_width
                    .checked_sub(by)
                    .ok_or_else(|| ReconstructError::MalformedStep {
                        rule: "bitblast_sign_extend".to_owned(),
                        detail: "sign_extend amount exceeds result width".to_owned(),
                    })?;
            if width_x == 0 {
                return Err(ReconstructError::MalformedStep {
                    rule: "bitblast_sign_extend".to_owned(),
                    detail: "zero-width sign_extend operand".to_owned(),
                });
            }
            let src = if i < width_x { i } else { width_x - 1 };
            let bit_term = operand_bit_term(x, src);
            return Ok(ctx.gate_term_to_prop(&bit_term));
        }
    }
    if let AletheTerm::App(head, args) = lhs {
        if head == "concat" {
            // `(concat a b)` (a high, b low): result bit `i` is `b_i` for
            // `i < width(b)`, else `a_{i - width(b)}` — the emitter emits the low
            // operand's bits first. Needs width(b), recovered from a recorded
            // bit-blasted leaf width or a literal's length.
            let [hi, lo] = args.as_slice() else {
                return Err(ReconstructError::UnsupportedTerm {
                    term: format!("concat needs two operands `{}`", lhs.key()),
                });
            };
            let width_lo =
                alethe_bv_width(ctx, lo).ok_or_else(|| ReconstructError::UnsupportedTerm {
                    term: format!("concat low-operand width unknown `{}`", lhs.key()),
                })?;
            // Bit-route into the operand structurally (`bv_bit`), so a compound concat
            // operand expands rather than becoming an opaque `@bit_of` projection.
            return if i < width_lo {
                bv_bit(ctx, lo, i)
            } else {
                bv_bit(ctx, hi, i - width_lo)
            };
        }
        if head == "bvcomp" {
            // `(bvcomp x y)`: a 1-bit result whose only bit is the per-bit-equality
            // AND over the operand bits. Needs the operand width (via `bv_widths`).
            let [x, y] = args.as_slice() else {
                return Err(ReconstructError::UnsupportedTerm {
                    term: format!("bvcomp needs two operands `{}`", lhs.key()),
                });
            };
            let width = alethe_bv_width(ctx, x)
                .or_else(|| alethe_bv_width(ctx, y))
                .ok_or_else(|| ReconstructError::UnsupportedTerm {
                    term: format!("bvcomp operand width unknown `{}`", lhs.key()),
                })?;
            if width == 0 {
                return Err(ReconstructError::MalformedStep {
                    rule: "bitblast_comp".to_owned(),
                    detail: "zero-width bvcomp operand".to_owned(),
                });
            }
            let bit_term = comp_bit_term(x, y, width);
            return Ok(ctx.gate_term_to_prop(&bit_term));
        }
    }
    bv_bit(ctx, lhs, i)
}

/// Bit 0 of `(bvcomp x y)` as an [`AletheTerm`]: the per-bit-equality AND
/// `(and (= x0 y0) … (= x_{w-1} y_{w-1}))` (or the single `(= x0 y0)` for width 1),
/// transcribing the emitter's `bitwise_equal_and`. `bvcomp` is a 1-bit result, so
/// this is its only bit.
fn comp_bit_term(x: &AletheTerm, y: &AletheTerm, width: usize) -> AletheTerm {
    let es: Vec<AletheTerm> = (0..width)
        .map(|i| {
            AletheTerm::App(
                "=".to_owned(),
                vec![operand_bit_term(x, i), operand_bit_term(y, i)],
            )
        })
        .collect();
    if es.len() > 1 {
        AletheTerm::App("and".to_owned(), es)
    } else {
        es.into_iter().next().expect("a bit-vector has width >= 1")
    }
}

/// The `Prop` `Iff (lhs_bit i) ⟦gadget_i⟧` for bit `i` of a term op.
fn bit_iff_prop(
    ctx: &mut ReconstructCtx,
    lhs: &AletheTerm,
    gadget_i: &AletheTerm,
    i: usize,
    result_width: usize,
) -> Result<ExprId, ReconstructError> {
    let lhs_bit = lhs_bit_prop(ctx, lhs, i, result_width)?;
    let gadget = gadget_bit_to_prop(ctx, gadget_i);
    Ok(ctx.mk_iff(lhs_bit, gadget))
}

/// The reflexive proof of [`bit_iff_prop`]. Sound only because `lhs_bit(i)` and
/// `⟦gadget_i⟧` are the **same** Prop under the pointwise bit model; the kernel
/// gate at the call site rejects if they ever diverge.
fn bit_iff_refl(
    ctx: &mut ReconstructCtx,
    lhs: &AletheTerm,
    gadget_i: &AletheTerm,
    i: usize,
    result_width: usize,
) -> Result<ExprId, ReconstructError> {
    let lhs_bit = lhs_bit_prop(ctx, lhs, i, result_width)?;
    let _ = gadget_i;
    Ok(ctx.mk_iff_refl(lhs_bit))
}

/// Extract the `(lhs, rhs)` operands of a `bitblast_*` step's single positive
/// `(= lhs rhs)` conclusion literal.
fn bitblast_conclusion_sides<'a>(
    rule: &str,
    conclusion: &'a [AletheLit],
) -> Result<(&'a AletheTerm, &'a AletheTerm), ReconstructError> {
    let [lit] = conclusion else {
        return Err(ReconstructError::MalformedStep {
            rule: rule.to_owned(),
            detail: format!(
                "expected one conclusion literal, found {}",
                conclusion.len()
            ),
        });
    };
    if lit.negated {
        return Err(ReconstructError::MalformedStep {
            rule: rule.to_owned(),
            detail: "conclusion literal is negated".to_owned(),
        });
    }
    match &lit.atom {
        AletheTerm::App(head, args) if head == "=" && args.len() == 2 => Ok((&args[0], &args[1])),
        _ => Err(ReconstructError::MalformedStep {
            rule: rule.to_owned(),
            detail: "conclusion is not a positive equality `(= lhs rhs)`".to_owned(),
        }),
    }
}

/// The bit operands of a `(@bbterm b0 … b_{n-1})` term, or [`None`] if `term` is
/// not a `@bbterm` application.
fn bbterm_bits(term: &AletheTerm) -> Option<&[AletheTerm]> {
    match term {
        AletheTerm::App(head, args) if head == "@bbterm" => Some(args),
        _ => None,
    }
}

/// Reconstruct a **complete bitwise `QF_BV` `unsat` proof** (as emitted by
/// [`crate::prove_qf_bv_unsat_alethe`]) into a Lean proof term of type `False`
/// that the trusted [`Kernel`] type-checks.
///
/// This wires the slice-5 bit-blast layer to the slice-3 (resolution) and slice-4
/// (Tseitin CNF-introduction) layers. The full proof has three strata:
///
/// 1. a **bit-blast bridge** — `bitblast_*` steps concluding `(= t bbform)`,
///    chained by `cong`/`trans` and turned into bit-level Boolean unit clauses by
///    `equiv1`/`equiv2` + `resolution`;
/// 2. the **Tseitin CNF-introduction** tautologies (`and_pos`/`and_neg`/`or_*`/
///    `equiv_*`/`xor_*`) over the bit-level gates (slice 4);
/// 3. the **clausal resolution** refutation down to `(cl)` (slice 3).
///
/// ### What is reconstructed — the fully-fused closed proof (slice 6)
///
/// The whole bitwise refutation is reconstructed genuinely, and the final `False`
/// term is **closed over only the input-assumption hypotheses and `em`** — there is
/// **no** bridge axiom for `cong`/`trans`/`equiv1`/`equiv2`/`bitblast_*`.
///
/// The fusion models each input bit-vector **predicate** directly in its bit-level
/// `Prop` form. From the proof's `equiv1`/`equiv2` bridge clauses we learn, for each
/// predicate atom `pred = (= s t)`, its bit-level Boolean form `B` (the `equiv`
/// clause literally pairs `pred` with `B`). We register `pred ↦ B` in the context's
/// `bridge`, putting the clausal/gate translation into **bit mode**: every
/// occurrence of `pred` now translates to `⟦B⟧` (its `Prop` *is* its bit form). Then:
///
/// - an input `assume (= s t)` becomes a hypothesis `h : ⟦B⟧` directly — the bit
///   unit the refutation needs, no `equiv1`/`cong`/`trans` axiom;
/// - `equiv1` (clause `¬pred ∨ B`) and `equiv2` (clause `pred ∨ ¬B`) translate to
///   `¬⟦B⟧ ∨ ⟦B⟧` / `⟦B⟧ ∨ ¬⟦B⟧`, which are genuine `Prop` tautologies — proved
///   classically via `em`, not assumed;
/// - the `bitblast_*`/`cong`/`trans` steps conclude term-level `(= t bbform)`
///   equalities that are *never consumed by the refutation* (only the predicate-level
///   `equiv` clauses feed resolution), so they need no proof at all — their bit-iff
///   content is still separately kernel-checked up front (the slice-5 obligation);
/// - the CNF-introduction tautologies are slice-4 structural proofs and resolution
///   is the slice-3 constructive binary core, both now operating on the *same*
///   bit-level `Prop`s as the assumptions.
///
/// The closing `(cl)` is `infer`-checked against `False` — the trusted gate — and
/// (the new bar) [`ReconstructCtx::declared_axiom_roles`] then contains only
/// `"assume"` and `"em"`. A wrong gadget bit, wrong resolvent, or non-tautological
/// `equiv` clause makes a per-step kernel gate fire — never a wrong `False`.
///
/// # Errors
///
/// Returns a [`ReconstructError`] for any command shape outside this bitwise
/// fragment (a non-bitwise `bitblast_*` rule, an unknown premise, a resolution or
/// gate shape the slices do not handle), or a kernel rejection. It never panics.
pub fn reconstruct_qf_bv_proof(
    ctx: &mut ReconstructCtx,
    commands: &[AletheCommand],
) -> Result<ExprId, ReconstructError> {
    // First, verify every BITWISE `bitblast_*` step's conclusion reconstructs to a
    // kernel-checked bit-iff term (the slice-5 soundness obligation). A non-bitwise
    // `bitblast_*` rule (carry chain, shift, structural) is rejected here. This is
    // also where a non-bitwise `QF_BV` proof is cleanly rejected.
    for cmd in commands {
        if let AletheCommand::Step { rule, clause, .. } = cmd {
            if rule.starts_with("bitblast_") {
                // Reconstruct-and-check; bitwise rules pass, others error out.
                reconstruct_bitblast_step(ctx, rule, clause)?;
            }
        }
    }

    // Learn the predicate → bit-form bridge from the `equiv1`/`equiv2` steps, then
    // run the clausal walk in bit mode so every predicate is its bit-level `Prop`.
    let bridge = collect_bitblast_bridge(commands);
    ctx.bridge = Some(bridge);
    ctx.gate_memo.clear(); // gate Props depend on the bridge; invalidate the cache.
    let result = reconstruct_bitwise_clausal(ctx, commands);
    ctx.bridge = None;
    ctx.gate_memo.clear();
    result
}

/// Reconstruct a **`QF_UFBV` Ackermann certificate** (the shape
/// [`crate::prove_qf_ufbv_unsat_alethe`] emits) into a kernel-checked `False`,
/// with **no trusted reduction step**.
///
/// The certificate composes an EUF congruence head — deriving each
/// functional-consistency consequent `(= v_i v_j)` from the abstraction's
/// defining equations and the argument equalities via `eq_congruent` +
/// `eq_transitive` — with a bit-blast tail that refutes the reduced `QF_BV`
/// problem. Both strata are reconstructed and gated by the **trusted kernel**:
///
/// 1. **Head (EUF, the closed trust hole).** For each spliced congruence block
///    (`!cong_*` ids concluding a consequent `(= v_i v_j)` under a tail-assume
///    id), a standalone EUF refutation `{defs, arg-eqs, ¬(= v_i v_j)}` is
///    reconstructed via [`reconstruct_qf_uf_proof`] to a kernel-checked `False`.
///    This is the certificate's new content: the previously-*trusted*
///    consistency constraint is now **kernel-derived** by congruence — a wrong
///    congruence makes the kernel reject (never a wrong "checked").
/// 2. **Tail (bit-blast).** The congruence blocks are collapsed back to plain
///    `assume`s of their consequents, and the resulting reduced `QF_BV`
///    refutation is reconstructed via [`reconstruct_qf_bv_proof`] to a
///    kernel-checked `False` — the returned term.
///
/// The two strata meet at the consequent atoms `(= v_i v_j)`: the head proves
/// them (kernel-checked) and the tail consumes them (kernel-checked), so an
/// Ackermann-decided `QF_UFBV` `unsat` carries a machine-checkable proof with no
/// trusted reduction. The returned `ExprId` is the tail's `False`; the head
/// obligations are kernel-verified as a precondition (an `Err` if any fails).
///
/// # Errors
///
/// Returns a [`ReconstructError`] if the proof is not in the certificate shape
/// (no `!cong_*` congruence blocks), if any EUF head obligation fails to
/// reconstruct/kernel-check, or if the bit-blast tail fails — never panics.
pub fn reconstruct_qf_ufbv_proof(
    ctx: &mut ReconstructCtx,
    commands: &[AletheCommand],
) -> Result<ExprId, ReconstructError> {
    let blocks = collect_congruence_blocks(commands);
    if blocks.is_empty() {
        return Err(ReconstructError::UnsupportedRule {
            rule: "reconstruct_qf_ufbv_proof: no `!cong_*` Ackermann congruence \
                   blocks (not a QF_UFBV certificate)"
                .to_owned(),
        });
    }

    // 1. Kernel-check each congruence head: the consistency constraint is derived
    //    by congruence, not trusted. A fresh ctx per obligation keeps the EUF
    //    α-world atoms from colliding with the bit-blast tail's bit atoms.
    for block in &blocks {
        let euf = block.euf_refutation();
        let mut head_ctx = ReconstructCtx::new();
        reconstruct_qf_uf_proof(&mut head_ctx, &euf)?;
    }

    // 2. Collapse the congruence blocks to plain consequent `assume`s and
    //    reconstruct the bit-blast tail to `False`.
    let tail = collapse_congruence_blocks(commands, &blocks);
    reconstruct_qf_bv_proof(ctx, &tail)
}

/// One spliced congruence block: the `!cong_*` head commands deriving a
/// consequent `(= v_i v_j)`, plus the tail consequent step's id/clause/premises.
struct CongruenceBlock {
    /// The tail id (e.g. `h3`) of the step concluding `(cl (= v_i v_j))`.
    consequent_id: String,
    /// The consequent equality literals `(= v_i v_j)`.
    consequent: Vec<AletheLit>,
    /// The `!cong_*` head commands (assumes + `eq_*`/`resolution` steps).
    head: Vec<AletheCommand>,
    /// The premise ids of the final consequent-producing resolution (the
    /// `eq_transitive` step plus its threaded unit equalities).
    final_premises: Vec<String>,
}

impl CongruenceBlock {
    /// A standalone EUF refutation of this congruence: the head's `assume`s
    /// (defs + arg-eqs), its `eq_*` theory steps and threading resolutions, plus
    /// a `¬(= v_i v_j)` assume and a closing resolution to `(cl)`. Reconstructable
    /// by [`reconstruct_qf_uf_proof`].
    fn euf_refutation(&self) -> Vec<AletheCommand> {
        let mut out = self.head.clone();
        // Re-emit the consequent-producing resolution under a private id (the
        // original tail id is not present in this standalone sub-proof).
        let consequent_step_id = "!cong_consequent".to_owned();
        out.push(AletheCommand::Step {
            id: consequent_step_id.clone(),
            clause: self.consequent.clone(),
            rule: "resolution".to_owned(),
            premises: self.final_premises.clone(),
            args: Vec::new(),
        });
        let negated: Vec<AletheLit> = self
            .consequent
            .iter()
            .map(|l| AletheLit {
                atom: l.atom.clone(),
                negated: !l.negated,
            })
            .collect();
        let diseq_id = "!cong_diseq".to_owned();
        out.push(AletheCommand::Assume {
            id: diseq_id.clone(),
            clause: negated,
        });
        out.push(AletheCommand::Step {
            id: "!cong_close".to_owned(),
            clause: Vec::new(),
            rule: "resolution".to_owned(),
            premises: vec![consequent_step_id, diseq_id],
            args: Vec::new(),
        });
        out
    }
}

/// Scan a certificate proof for the spliced congruence blocks: contiguous runs of
/// `!cong_*` commands followed by the consequent step (a non-`!cong_*` `Step`
/// whose premises reference a `!cong_trans_*`).
fn collect_congruence_blocks(commands: &[AletheCommand]) -> Vec<CongruenceBlock> {
    let mut blocks: Vec<CongruenceBlock> = Vec::new();
    let mut head: Vec<AletheCommand> = Vec::new();
    for cmd in commands {
        let (id, premises): (&str, Vec<String>) = match cmd {
            AletheCommand::Assume { id, .. } => (id.as_str(), Vec::new()),
            AletheCommand::Step { id, premises, .. } => (id.as_str(), premises.clone()),
        };
        if id.starts_with("!cong_") {
            head.push(cmd.clone());
            continue;
        }
        // A non-`!cong_*` command. If it is the consequent step (references a
        // `!cong_trans_*` premise), it closes the current head block.
        let closes = premises.iter().any(|p| p.starts_with("!cong_trans_"));
        if closes
            && !head.is_empty()
            && let AletheCommand::Step {
                id,
                clause,
                premises,
                ..
            } = cmd
        {
            blocks.push(CongruenceBlock {
                consequent_id: id.clone(),
                consequent: clause.clone(),
                head: std::mem::take(&mut head),
                final_premises: premises.clone(),
            });
        }
    }
    blocks
}

/// Test-only accessor for a congruence block's standalone EUF head refutation
/// (the route-A audit reconstructs it directly to inspect its declared axioms).
#[cfg(test)]
fn euf_refutation_for_test(block: &CongruenceBlock) -> Vec<AletheCommand> {
    block.euf_refutation()
}

/// Rebuild the proof with every congruence block collapsed to a plain `assume`
/// of its consequent (under the original tail id), yielding the reduced `QF_BV`
/// refutation that [`reconstruct_qf_bv_proof`] reconstructs.
fn collapse_congruence_blocks(
    commands: &[AletheCommand],
    blocks: &[CongruenceBlock],
) -> Vec<AletheCommand> {
    let consequent_ids: BTreeMap<&str, &CongruenceBlock> = blocks
        .iter()
        .map(|b| (b.consequent_id.as_str(), b))
        .collect();
    let mut out: Vec<AletheCommand> = Vec::with_capacity(commands.len());
    for cmd in commands {
        let id = match cmd {
            AletheCommand::Assume { id, .. } | AletheCommand::Step { id, .. } => id.as_str(),
        };
        if id.starts_with("!cong_") {
            continue; // head command, dropped
        }
        if let Some(block) = consequent_ids.get(id) {
            // The consequent step becomes a plain assume of `(= v_i v_j)`.
            out.push(AletheCommand::Assume {
                id: block.consequent_id.clone(),
                clause: block.consequent.clone(),
            });
        } else {
            out.push(cmd.clone());
        }
    }
    out
}

/// Scan the proof for `equiv1`/`equiv2` bridge clauses and learn, for each
/// bit-vector predicate atom, its bit-level Boolean form `B`.
///
/// The emitter's `equiv1` concludes `(cl (not pred) B)` and `equiv2` concludes
/// `(cl pred (not B))` — each clause pairs the predicate atom `pred` (a `(= s t)`
/// over bit-vector terms) with its bit form `B` (a Boolean over bit projections).
/// We read `pred ↦ B` straight from the clause: the predicate is the literal whose
/// atom is a `(= …)` over non-bit operands (it carries a `bvand`/`bvor`/… or a bare
/// bit-vector symbol), and `B` is the other literal's atom. This avoids tracing the
/// `cong`/`trans` chain — the `equiv` clause already exhibits the correspondence.
fn collect_bitblast_bridge(commands: &[AletheCommand]) -> BTreeMap<String, AletheTerm> {
    let mut bridge: BTreeMap<String, AletheTerm> = BTreeMap::new();
    for cmd in commands {
        let AletheCommand::Step { rule, clause, .. } = cmd else {
            continue;
        };
        if rule != "equiv1" && rule != "equiv2" {
            continue;
        }
        // The equiv clause is a 2-literal pairing of `pred` and `B`. Identify which
        // literal is the bit-vector predicate (it mentions a `@bit_of`-free
        // bit-vector operand) and which is the bit-level form.
        let [l0, l1] = clause.as_slice() else {
            continue;
        };
        let (pred, b_form) = if is_bv_predicate_atom(&l0.atom) {
            (&l0.atom, &l1.atom)
        } else if is_bv_predicate_atom(&l1.atom) {
            (&l1.atom, &l0.atom)
        } else {
            continue;
        };
        bridge.insert(pred.key(), b_form.clone());
    }
    bridge
}

/// Whether an atom is a bit-vector **predicate** `(= s t)` whose operands are
/// bit-vector *terms* (a bare symbol or a `bv…`/structural application), as opposed
/// to a bit-level Boolean `(= a_i b_i)` over `@bit_of` projections. The discriminator
/// is that at least one operand is **not** an `@bit_of` projection (nor a Boolean
/// gate / Boolean constant): a genuine bit-vector term.
fn is_bv_predicate_atom(term: &AletheTerm) -> bool {
    match term {
        // Bit-vector equality (`=` over BV operands) and the comparison predicates
        // (`bvult`/`bvslt`) whose bit-level form `B` is a ladder. Each carries a
        // `pred ↔ B` bridge entry so its `equiv1`/`equiv2` clause is reconstructed
        // as the tautology `¬B ∨ B` over the bit atoms.
        AletheTerm::App(head, args)
            if (head == "=" || head == "bvult" || head == "bvslt") && args.len() == 2 =>
        {
            args.iter().any(is_bitvector_operand)
        }
        _ => false,
    }
}

/// Whether a term is a bit-vector operand (a bare symbol that is not a Boolean
/// literal, or a `bv…` application), distinguishing a predicate's BV operand from a
/// bit-level Boolean leaf (`@bit_of` projection, `and`/`or`/`xor`/`not`/`=` gate).
fn is_bitvector_operand(term: &AletheTerm) -> bool {
    match term {
        AletheTerm::Const(s) => s != "true" && s != "false" && !s.starts_with("#b"),
        AletheTerm::App(head, _) => head.starts_with("bv") || head == "concat" || head == "@bbterm",
        AletheTerm::Indexed { .. } => false,
    }
}

/// The fused clausal walk for a bitwise `QF_BV` proof: a superset of
/// [`reconstruct_resolution_proof`] that threads the bit-blast bridge rules under
/// the context's **bit mode** (`bridge` set), so the reconstructed `False` is closed
/// over only the input-assumption hypotheses and `em`.
///
/// Each command becomes a [`Clause`] (its literals + a kernel proof of the clause's
/// bit-level `Prop` encoding). `assume` is the input predicate hypothesis (its
/// `Prop` is the predicate's bit form, via the bridge); `resolution` is the slice-3
/// constructive core; the CNF-introduction rules are the slice-4 structural
/// tautologies; `equiv1`/`equiv2` are genuine `¬B ∨ B` tautologies; the
/// `cong`/`trans`/`bitblast_*` term-equality steps are deferred (never consumed by
/// the refutation, so never forced into the `False` term). The final `(cl)` is
/// checked against `False`.
fn reconstruct_bitwise_clausal(
    ctx: &mut ReconstructCtx,
    commands: &[AletheCommand],
) -> Result<ExprId, ReconstructError> {
    let _ = ctx.em_axiom();
    let mut env: BTreeMap<String, Clause> = BTreeMap::new();

    for cmd in commands {
        match cmd {
            AletheCommand::Assume { id, clause } => {
                let prop = ctx.clause_to_prop(clause);
                let proof = fresh_axiom(ctx, prop, "assume")?;
                env.insert(
                    id.clone(),
                    Clause {
                        lits: clause.clone(),
                        proof,
                    },
                );
            }
            AletheCommand::Step {
                id,
                clause,
                rule,
                premises,
                ..
            } => {
                let recovered = reconstruct_bitwise_step(ctx, rule, clause, premises, &env)?;
                if let Some(recovered) = recovered {
                    if clause.is_empty() {
                        return check_false_prop(ctx, recovered.proof);
                    }
                    env.insert(id.clone(), recovered);
                }
            }
        }
    }
    Err(ReconstructError::NoEmptyClause)
}

/// Reconstruct one step of the fused bitwise clausal walk.
///
/// Returns `Ok(Some(clause))` for a step that contributes a clause to the
/// refutation, or `Ok(None)` for a **deferred** term-level bridge step
/// (`cong`/`trans`/`bitblast_*`) that the refutation never consumes — those carry no
/// reconstructed proof, so they introduce no axiom into the final `False` term.
fn reconstruct_bitwise_step(
    ctx: &mut ReconstructCtx,
    rule: &str,
    clause: &[AletheLit],
    premises: &[String],
    env: &BTreeMap<String, Clause>,
) -> Result<Option<Clause>, ReconstructError> {
    match rule {
        // Slice-3 resolution core (also closes to `(cl)`).
        "resolution" | "th_resolution" => {
            // A compound term's **bit-definition** unit `(cl B_t)` is emitted as
            // `equiv1` + `resolution` against the (deferred) `bitblast_*` term-equality
            // step, so one premise is not in `env`. Under the faithful bit model the
            // definition `B_t = (and (= ((_ @bit_of i) t) g_i) …)` is a conjunction of
            // *reflexive* iffs (`((_ @bit_of i) t)` resolves structurally to the same
            // Prop as `g_i`), hence a tautology proved directly — no premise needed.
            if premises.iter().any(|p| !env.contains_key(p)) {
                if let Some(def) = try_reconstruct_bit_definition(ctx, clause)? {
                    return Ok(Some(def));
                }
            }
            Ok(Some(reconstruct_resolution_step(
                ctx, clause, premises, env,
            )?))
        }
        // Slice-4 Tseitin CNF-introduction tautologies, proved structurally.
        "and_pos" | "and_neg" | "or_pos" | "or_neg" | "equiv_pos1" | "equiv_pos2"
        | "equiv_neg1" | "equiv_neg2" | "xor_pos1" | "xor_pos2" | "xor_neg1" | "xor_neg2" => {
            let proof = reconstruct_cnf_intro_rule(ctx, rule, clause)?;
            Ok(Some(Clause {
                lits: clause.to_vec(),
                proof,
            }))
        }
        // The predicate↔bit-form bridge. Under bit mode `⟦pred⟧ ≡ ⟦B⟧`, so the
        // `equiv1`/`equiv2` clause `(¬pred ∨ B)` / `(pred ∨ ¬B)` is a genuine
        // `Prop` tautology — proved classically (via `em`), not assumed.
        "equiv1" | "equiv2" => Ok(Some(reconstruct_equiv_bridge(ctx, rule, clause)?)),
        // The Boolean-constant pins the emitter feeds into the SAT refutation when a
        // carry-chain gadget (`bvadd`/`bvneg`/`bvmul`, the Route-2 `bvsub` rewrite)
        // embeds a literal `true`/`false` operand:
        //   `true`  → `(cl true)`      : Prop `True`,     proved by `True.intro`.
        //   `false` → `(cl (not false))`: Prop `Not False`, proved by `fun h => h`.
        // Both are closed tautologies (no axiom enters the `False` term).
        "true" | "false" => Ok(Some(reconstruct_bool_const_pin(ctx, rule, clause)?)),
        // Term-level bridge steps that the refutation never consumes (only the
        // predicate-level `equiv` clauses feed resolution). Defer them: no proof is
        // built, so no axiom is introduced. Their bit-iff content is separately
        // kernel-checked in `reconstruct_qf_bv_proof`.
        //
        // `bv_poly_simp` is the Route-2 `bvsub`-rewrite bridge: the term equality
        // `(= (bvsub a b) (bvadd a (bvneg b)))` Carcara validates (polynomial-equal
        // mod 2^w). The refutation consumes it only via the `trans`-chained term
        // equality `(= (bvsub a b) bbform)`, whose bit content is the `bvsub`
        // bit-definition (reflexive under the faithful `bv_bit` model, where
        // `bvsub a b` bit `i` IS the `bvadd a (bvneg b)` bit). So, like `cong`/`trans`,
        // it is deferred: no axiom enters the `False` term.
        "cong" | "trans" | "bv_poly_simp" => Ok(None),
        r if r.starts_with("bitblast_") => Ok(None),
        other => Err(ReconstructError::UnsupportedRule {
            rule: other.to_owned(),
        }),
    }
}

/// Try to reconstruct a compound term's **bit-definition** unit clause `(cl B_t)`,
/// where `B_t = (and (= ((_ @bit_of i) t) g_i) …)` (or the single `(= … g_0)` for a
/// width-1 term) ties each projection `((_ @bit_of i) t)` to its gadget bit `g_i`.
///
/// Under the faithful bit model, `((_ @bit_of i) t)` for a compound `t` resolves
/// structurally (via [`bv_bit`], the same path the gadget `g_i` takes), so each
/// conjunct `(= ((_ @bit_of i) t) g_i)` is `Iff P P` — a reflexive identity. The
/// whole `B_t` is therefore an `And`-fold of `Iff.refl`s, proved directly with no
/// premise. The result is `check_against`-gated: if any conjunct is NOT reflexive
/// (a wrong gadget bit), the kernel rejects.
///
/// Returns `Ok(None)` if `clause` is not a single positive bit-definition literal,
/// so the caller falls back to ordinary resolution.
fn try_reconstruct_bit_definition(
    ctx: &mut ReconstructCtx,
    clause: &[AletheLit],
) -> Result<Option<Clause>, ReconstructError> {
    // Must be a single positive literal `B_t`.
    let [lit] = clause else {
        return Ok(None);
    };
    if lit.negated {
        return Ok(None);
    }
    // Collect the conjuncts of `B_t`: either `(and c0 c1 …)` or a single `c0`.
    let conjuncts: Vec<&AletheTerm> = match &lit.atom {
        AletheTerm::App(head, args) if head == "and" && !args.is_empty() => args.iter().collect(),
        single @ AletheTerm::App(head, _) if head == "=" => vec![single],
        _ => return Ok(None),
    };
    // Every conjunct must be a bit-definition equality `(= ((_ @bit_of i) t) g_i)`
    // whose left side projects a COMPOUND term (not a bare symbol — that would be an
    // ordinary predicate's bit form, not a definition).
    let mut defines_compound = false;
    for c in &conjuncts {
        let AletheTerm::App(head, args) = c else {
            return Ok(None);
        };
        if head != "=" || args.len() != 2 {
            return Ok(None);
        }
        match &args[0] {
            AletheTerm::Indexed {
                op, args: pargs, ..
            } if op == "@bit_of" && pargs.len() == 1 => {
                if !matches!(pargs[0], AletheTerm::Const(_)) {
                    defines_compound = true;
                }
            }
            _ => return Ok(None),
        }
    }
    if !defines_compound {
        return Ok(None);
    }

    // Build the proof: each conjunct's `Prop` is `Iff ⟦lhs⟧ ⟦rhs⟧`; under the model
    // `⟦lhs⟧` and `⟦rhs⟧` coincide, so its proof is `mk_iff_refl(⟦lhs⟧)`. `And.intro`
    // fold (right-nested) the per-conjunct refl proofs.
    let mut props: Vec<ExprId> = Vec::with_capacity(conjuncts.len());
    let mut proofs: Vec<ExprId> = Vec::with_capacity(conjuncts.len());
    for c in &conjuncts {
        let AletheTerm::App(_, args) = c else {
            return Ok(None);
        };
        let lhs_prop = ctx.gate_term_to_prop(&args[0]);
        let rhs_prop = ctx.gate_term_to_prop(&args[1]);
        props.push(ctx.mk_iff(lhs_prop, rhs_prop));
        // The reflexive proof of `Iff lhs rhs` is well-typed only if `lhs`/`rhs`
        // coincide as Props; the final `check_against` is the gate.
        proofs.push(ctx.mk_iff_refl(lhs_prop));
    }
    // Right-fold `And.intro`.
    let n = props.len();
    let mut acc_prop = props[n - 1];
    let mut acc_proof = proofs[n - 1];
    for i in (0..n - 1).rev() {
        acc_proof = and_intro(ctx, props[i], acc_prop, proofs[i], acc_proof);
        acc_prop = ctx.mk_and(props[i], acc_prop);
    }
    let target = ctx.gate_clause_to_prop(clause);
    let proof = check_against(ctx, "bit_definition", acc_proof, target)?;
    Ok(Some(Clause {
        lits: clause.to_vec(),
        proof,
    }))
}

/// Reconstruct an `equiv1`/`equiv2` bridge clause as a genuine bit-level `Prop`
/// tautology under bit mode.
///
/// In bit mode the predicate atom `pred` translates to its bit form `⟦B⟧`, so the
/// `equiv1` clause `(cl (not pred) B)` is `¬⟦B⟧ ∨ ⟦B⟧` and the `equiv2` clause
/// `(cl pred (not B))` is `⟦B⟧ ∨ ¬⟦B⟧` — both `Prop` tautologies. We prove them with
/// the same classical case-split engine the CNF-introduction tautologies use
/// ([`prove_clause_by_cases`]): the clause is a tautology over its (bit-level) atoms,
/// so the engine finds a satisfied literal in every assignment. The result is
/// `check_against`-gated to the clause's bit-level `Prop` encoding.
///
/// If the clause is not a `¬X ∨ X` tautology under bit mode (e.g. the bridge map did
/// not identify the predicate, so the two literals are unrelated atoms), the
/// case-split engine fails and a [`ReconstructError::MalformedStep`] surfaces — never
/// a silently-assumed bridge.
fn reconstruct_equiv_bridge(
    ctx: &mut ReconstructCtx,
    rule: &str,
    clause: &[AletheLit],
) -> Result<Clause, ReconstructError> {
    let _ = ctx.em_axiom();

    // The case-split atoms: the distinct gate leaves of the (bridge-substituted)
    // clause. Substitute each literal's atom through the bridge so `collect_atoms`
    // (which is not itself bridge-aware) decomposes the bit form, not the opaque
    // predicate.
    let substituted: Vec<AletheLit> = clause
        .iter()
        .map(|lit| AletheLit {
            atom: ctx.bridge_substitute(&lit.atom),
            negated: lit.negated,
        })
        .collect();

    // The bridge clause is `¬pred ∨ B` (equiv1) / `pred ∨ ¬B` (equiv2); after
    // substitution both literals share the atom `B`, so the tautology is just
    // `¬⟦B⟧ ∨ ⟦B⟧`, provable by `em ⟦B⟧`. Case-split over the substituted literal
    // atoms THEMSELVES (treated as opaque via `prove_term`'s assignment-first
    // lookup), not their bit leaves — `collect_atoms` would recurse into `B` and
    // give a `2^leaves` split over the ladder.
    let mut atom_keys: Vec<(String, AletheTerm)> = Vec::new();
    let mut seen = std::collections::BTreeSet::new();
    for lit in &substituted {
        let k = lit.atom.key();
        if seen.insert(k.clone()) {
            atom_keys.push((k, lit.atom.clone()));
        }
    }

    // The target is the ORIGINAL clause's bit-level `Prop` (predicate atoms route
    // through the bridge inside `gate_clause_to_prop`); the substituted clause has
    // the identical `Prop`, so proving over the substituted form yields a term of
    // the target type.
    let target = ctx.gate_clause_to_prop(clause);
    let mut assignment = Assignment::new();
    let proof = prove_clause_by_cases(ctx, &atom_keys, 0, &mut assignment, &substituted, target)?;
    let proof = check_against(ctx, rule, proof, target)?;
    Ok(Clause {
        lits: clause.to_vec(),
        proof,
    })
}

/// Reconstruct a Boolean-constant pin clause — the Carcara `true`/`false` tautology
/// the emitter feeds into the SAT refutation to fix a carry-chain gadget's literal
/// `true`/`false` operand:
///
/// - `true` → clause `(cl true)`, Prop `True`, proof `True.intro`;
/// - `false` → clause `(cl (not false))`, Prop `Not False` (i.e. `False → False`),
///   proof the identity `fun (h : False) => h`.
///
/// Both are closed (no axiom/hypothesis), `check_against`-gated to the clause's `Prop`.
fn reconstruct_bool_const_pin(
    ctx: &mut ReconstructCtx,
    rule: &str,
    clause: &[AletheLit],
) -> Result<Clause, ReconstructError> {
    let target = ctx.gate_clause_to_prop(clause);
    let raw = match rule {
        "true" => ctx.kernel.const_(ctx.prelude.true_intro, vec![]),
        "false" => {
            // `fun (h : False) => h : False → False`, defeq `Not False`.
            let anon = ctx.kernel.anon();
            let false_const = ctx.kernel.const_(ctx.prelude.false_, vec![]);
            let body = ctx.kernel.bvar(0);
            ctx.kernel.lam(anon, false_const, body, BinderInfo::Default)
        }
        _ => {
            return Err(ReconstructError::UnsupportedRule {
                rule: rule.to_owned(),
            });
        }
    };
    let proof = check_against(ctx, rule, raw, target)?;
    Ok(Clause {
        lits: clause.to_vec(),
        proof,
    })
}

impl ReconstructCtx {
    /// Rewrite an atom term through the bit-blast bridge: if its key names a
    /// registered bit-vector predicate, return its bit-level Boolean form `B`;
    /// otherwise return the term unchanged. Used to expose the bit-level structure
    /// to the (non-bridge-aware) tautology case-split engine.
    fn bridge_substitute(&self, term: &AletheTerm) -> AletheTerm {
        if let Some(bridge) = &self.bridge {
            if let Some(b_form) = bridge.get(&term.key()) {
                return b_form.clone();
            }
        }
        term.clone()
    }
}

// ===========================================================================
// LRA `la_generic` (Farkas) reconstruction (P3.7 arithmetic fragment, slice 1).
//
// A small real `QF_LRA` `unsat` instance's Farkas certificate is reconstructed
// into a Lean term of type `False` that the trusted kernel type-checks, over the
// axiomatized linear ordered field of `build_arith_prelude` (carrier `R`, ops
// `add`/`mul`/`neg`/`zero`/`one`, relations `le`/`lt`, the order/ring axioms).
//
// ## The model
//
// - Each real variable `xⱼ` ⇒ an opaque `R`-typed `Axiom` (declared lazily,
//   deterministically, by dense variable index).
// - A linear term `Σ aⱼ xⱼ + c` ⇒ an `R` expression built from `add`/`neg`/
//   `one`/`zero`. **Coefficient restriction (slice 1):** only small integer
//   coefficients in `{-1, 0, +1}` and a constant in `{0, 1}` are modelled (no
//   general rationals); a `±1` coefficient is `xⱼ` / `neg xⱼ`, and the constant
//   `1` is the prelude's `one`. Anything outside this is rejected, not guessed.
// - A constraint atom `t ⋈ c` (`≤`/`<`) ⇒ `le`/`lt` over the `R` expressions; an
//   input assumption is a hypothesis axiom of that exact `Prop`.
//
// ## What is reconstructed (slice 1): the transitivity-reducible refutation
//
// The bar is the baby-Farkas / order-chaining shape: a two-constraint instance
// `e ≤ 0 ∧ 1 ≤ e` (`e` a shared `R` expression). The refutation is **pure order
// chaining**, with NO ring sum:
//
//   step1 := le_trans one e zero h_lo h_hi : le one zero
//   step2 := lt_of_le_of_lt one zero one step1 zero_lt_one : lt one one
//   refute := lt_irrefl one step2 : False
//
// where `h_hi : le e zero` and `h_lo : le one e` are the input-constraint
// hypotheses. The general multi-variable / arbitrary-rational Farkas normalizer
// (scaling by `λ` and a ring cancellation `Σ λᵢ tᵢ = const`) is a LATER slice;
// out-of-scope cert shapes are rejected with a clear [`ReconstructError`].
//
// ## Soundness
//
// The kernel `infer`s the final term and requires it `def_eq` `False`. A wrong
// combination ⇒ the kernel rejects ⇒ [`ReconstructError::KernelRejected`], never
// a wrong `False`. The arith-prelude axioms are the (kernel-type-checked) trusted
// base; the only added axioms are the input-constraint hypotheses.
// ===========================================================================

use axeyum_ir::{
    ConstructorId, DatatypeId, Op as IrOp, Rational, Sort as IrSort, TermArena, TermId,
    TermNode as IrTermNode,
};
use axeyum_lean_kernel::{ArithPrelude, build_arith_prelude};

// The LRA reconstruction items below are the public API surface a `lib.rs`
// re-export will expose (mirroring the EUF `reconstruct_qf_uf_proof` re-export);
// until that re-export lands they are reachable only from this module's tests, so
// the crate-level dead-code lint flags them. The `allow(dead_code)` markers are
// scoped to these items (not the module) and become inert once re-exported.

/// A linear real expression `Σ aⱼ xⱼ + c` over dense variable indices, the
/// reconstruction-side mirror of the LRA collector's linear form. Coefficients and
/// the constant are exact [`Rational`]s; slice 1 only *reconstructs* the small
/// `{-1,0,+1}` coefficient / `{0,1}` constant subset into `R` (see [`LinR`]).
#[derive(Debug, Clone, Default, PartialEq, Eq)]
#[allow(dead_code)]
struct LinR {
    /// `(variable index, coefficient)` pairs, ascending, all coefficients nonzero.
    coeffs: Vec<(usize, Rational)>,
    /// The constant term.
    constant: Rational,
}

#[allow(dead_code)]
impl LinR {
    fn constant(value: Rational) -> Self {
        Self {
            coeffs: Vec::new(),
            constant: value,
        }
    }

    fn var(index: usize) -> Self {
        Self {
            coeffs: vec![(index, Rational::integer(1))],
            constant: Rational::zero(),
        }
    }

    /// Negate, declining (`None`) on any `i128` overflow during normalization.
    fn neg(&self) -> Option<Self> {
        let mut coeffs = Vec::with_capacity(self.coeffs.len());
        for &(i, c) in &self.coeffs {
            coeffs.push((i, c.checked_neg()?));
        }
        Some(Self {
            coeffs,
            constant: self.constant.checked_neg()?,
        })
    }

    /// Add, declining (`None`) on any `i128` overflow.
    fn add(&self, other: &Self) -> Option<Self> {
        let mut map: BTreeMap<usize, Rational> = BTreeMap::new();
        for &(i, c) in self.coeffs.iter().chain(&other.coeffs) {
            let e = map.entry(i).or_insert_with(Rational::zero);
            *e = e.checked_add(c)?;
        }
        let coeffs = map.into_iter().filter(|(_, c)| !c.is_zero()).collect();
        Some(Self {
            coeffs,
            constant: self.constant.checked_add(other.constant)?,
        })
    }

    fn sub(&self, other: &Self) -> Option<Self> {
        self.add(&other.neg()?)
    }

    /// Whether this is the linear expression of a single bare variable `xⱼ`
    /// (coefficient `+1`, no constant), returning its index.
    fn as_bare_var(&self) -> Option<usize> {
        match self.coeffs.as_slice() {
            [(i, c)] if *c == Rational::integer(1) && self.constant.is_zero() => Some(*i),
            _ => None,
        }
    }

    /// Whether this is the constant `value` (no variables).
    fn is_constant_eq(&self, value: Rational) -> bool {
        self.coeffs.is_empty() && self.constant == value
    }
}

/// The reconstruction context for LRA Farkas proofs: a [`Kernel`] seeded with the
/// arithmetic prelude (linear ordered field `R`), plus a deterministic map from a
/// dense real-variable index to its opaque `R`-typed [`NameId`].
///
/// Distinct from [`ReconstructCtx`] (the EUF carrier `α`): the carrier here is the
/// ordered field `R` and the trusted base is [`build_arith_prelude`]'s axioms.
#[allow(dead_code)]
pub struct LraReconstructCtx {
    kernel: Kernel,
    arith: ArithPrelude,
    /// Dense variable index → its opaque `R`-typed constant `NameId`.
    vars: BTreeMap<usize, NameId>,
    /// Monotone counter for fresh, collision-free declaration names.
    next_id: u64,
}

impl core::fmt::Debug for LraReconstructCtx {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("LraReconstructCtx")
            .field("vars", &self.vars.keys().collect::<Vec<_>>())
            .finish_non_exhaustive()
    }
}

impl Default for LraReconstructCtx {
    fn default() -> Self {
        Self::new()
    }
}

#[allow(dead_code)]
impl LraReconstructCtx {
    /// Build a fresh LRA reconstruction context: a kernel with the arithmetic
    /// prelude declared and an empty variable map.
    #[must_use]
    pub fn new() -> Self {
        let mut kernel = Kernel::new();
        let arith = build_arith_prelude(&mut kernel);
        Self {
            kernel,
            arith,
            vars: BTreeMap::new(),
            next_id: 0,
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

    /// The arithmetic prelude names (`R`, `le`, `lt`, `le_trans`, …).
    #[must_use]
    pub fn arith(&self) -> &ArithPrelude {
        &self.arith
    }

    /// Mint a fresh private name component under the anonymous root.
    fn fresh_name(&mut self, base: &str) -> NameId {
        let anon = self.kernel.anon();
        let ns = self.kernel.name_str(anon, "axeyum.reconstruct.lra");
        let id = self.next_id;
        self.next_id += 1;
        let with_base = self.kernel.name_str(ns, base);
        self.kernel.name_num(with_base, id)
    }

    /// Mint a fresh free-variable id for building open `Or.rec` minor-premise
    /// bodies (the disjunctive-LRA case split). Reuses the deterministic `next_id`
    /// counter; fvar ids live in a separate namespace from `NameId` declarations,
    /// so sharing the counter cannot collide.
    fn fresh_fvar_id(&mut self) -> u64 {
        let id = self.next_id;
        self.next_id += 1;
        id
    }

    /// Get (declaring lazily) the opaque `R`-typed constant for variable `index`.
    /// Idempotent: the same index always maps to the same constant.
    fn var_const(&mut self, index: usize) -> NameId {
        if let Some(&id) = self.vars.get(&index) {
            return id;
        }
        let r_ty = self.kernel.const_(self.arith.r, vec![]);
        let decl_name = self.fresh_name("x");
        self.kernel
            .add_declaration(Declaration::Axiom {
                name: decl_name,
                uparams: vec![],
                ty: r_ty,
            })
            .expect("real variable axiom (_ : R) should admit");
        self.vars.insert(index, decl_name);
        decl_name
    }

    /// `add x y : R`.
    fn mk_add(&mut self, x: ExprId, y: ExprId) -> ExprId {
        let add = self.kernel.const_(self.arith.add, vec![]);
        let e = self.kernel.app(add, x);
        self.kernel.app(e, y)
    }

    /// `mul x y : R`.
    fn mk_mul(&mut self, x: ExprId, y: ExprId) -> ExprId {
        let mul = self.kernel.const_(self.arith.mul, vec![]);
        let e = self.kernel.app(mul, x);
        self.kernel.app(e, y)
    }

    /// `neg x : R`.
    fn mk_neg(&mut self, x: ExprId) -> ExprId {
        let neg = self.kernel.const_(self.arith.neg, vec![]);
        self.kernel.app(neg, x)
    }

    /// `zero : R`.
    fn mk_zero(&mut self) -> ExprId {
        self.kernel.const_(self.arith.zero, vec![])
    }

    /// `one : R`.
    fn mk_one(&mut self) -> ExprId {
        self.kernel.const_(self.arith.one, vec![])
    }

    /// `le x y : Prop`.
    fn mk_le(&mut self, x: ExprId, y: ExprId) -> ExprId {
        let le = self.kernel.const_(self.arith.le, vec![]);
        let e = self.kernel.app(le, x);
        self.kernel.app(e, y)
    }

    fn mk_lt(&mut self, x: ExprId, y: ExprId) -> ExprId {
        let lt = self.kernel.const_(self.arith.lt, vec![]);
        let e = self.kernel.app(lt, x);
        self.kernel.app(e, y)
    }

    /// Build the `R` expression for a [`LinR`], restricted to the slice-1 small
    /// subset: integer coefficients in `{-1, 0, +1}` and a constant in `{0, 1}`.
    ///
    /// `Σ ±xⱼ (+ 1)` is a left-nested `add` over `xⱼ` / `neg xⱼ` terms (and a
    /// trailing `one` when the constant is `1`); a bare constant `0` is `zero`.
    ///
    /// # Errors
    ///
    /// Returns [`ReconstructError::UnsupportedTerm`] for any coefficient outside
    /// `{-1,0,+1}` or a constant outside `{0,1}` — the boundary of this slice.
    fn lin_to_r(&mut self, lin: &LinR) -> Result<ExprId, ReconstructError> {
        let one = Rational::integer(1);
        let neg_one = Rational::integer(-1);
        let mut terms: Vec<ExprId> = Vec::new();
        for &(index, coeff) in &lin.coeffs {
            let var_name = self.var_const(index);
            let var = self.kernel.const_(var_name, vec![]);
            if coeff == one {
                terms.push(var);
            } else if coeff == neg_one {
                let neg = self.mk_neg(var);
                terms.push(neg);
            } else {
                return Err(ReconstructError::UnsupportedTerm {
                    term: format!(
                        "LRA reconstruction (slice 1) only models ±1 coefficients; \
                         got {}/{} on variable {index}",
                        coeff.numerator(),
                        coeff.denominator()
                    ),
                });
            }
        }
        if lin.constant == one {
            let one_r = self.mk_one();
            terms.push(one_r);
        } else if !lin.constant.is_zero() {
            return Err(ReconstructError::UnsupportedTerm {
                term: format!(
                    "LRA reconstruction (slice 1) only models a constant of 0 or 1; got {}/{}",
                    lin.constant.numerator(),
                    lin.constant.denominator()
                ),
            });
        }
        // Fold the terms with `add`; an empty term list is `zero`.
        let mut iter = terms.into_iter();
        let Some(first) = iter.next() else {
            return Ok(self.mk_zero());
        };
        let mut acc = first;
        for t in iter {
            acc = self.mk_add(acc, t);
        }
        Ok(acc)
    }

    /// Declare a fresh hypothesis axiom `h : prop` and return its `Const` proof.
    fn hyp_axiom(&mut self, prop: ExprId) -> Result<ExprId, ReconstructError> {
        let name = self.fresh_name("hyp");
        self.kernel
            .add_declaration(Declaration::Axiom {
                name,
                uparams: vec![],
                ty: prop,
            })
            .map_err(|e| ReconstructError::KernelRejected {
                rule: "la_generic".to_owned(),
                detail: format!("hypothesis axiom did not admit: {e:?}"),
            })?;
        Ok(self.kernel.const_(name, vec![]))
    }

    // -----------------------------------------------------------------------
    // General-Farkas ring engine.
    //
    // The general la_generic reconstruction (any nonneg integer multipliers over
    // integer-coefficient `≤`-constraints) needs to manipulate linear `R`
    // expressions up to the ordered-field axioms. Since `R` is axiomatic the kernel
    // never *computes* `λ·L = c`; every cancellation is an explicit `Eq`-rewrite
    // built from `add_comm`/`add_assoc`/`add_neg`/`add_zero`. The helpers below are
    // that explicit ring layer: `Eq R`-combinators (`refl`/`symm`/`trans`/`congr_add`),
    // a canonical additive normal form, and a normalizer that *proves* every linear
    // expression equal to the canonical form of its [`LinR`]. Two ring-equal
    // expressions then normalize to the **same** interned canonical term, so their
    // equality is `trans normA (symm normB)` — kernel-checked end to end.
    // -----------------------------------------------------------------------

    /// `Eq R x y` (the carrier-level equality proposition).
    fn mk_eq_r(&mut self, x: ExprId, y: ExprId) -> ExprId {
        let one_lvl = {
            let z = self.kernel.level_zero();
            self.kernel.level_succ(z)
        };
        let eq = self.kernel.const_(self.arith.logic.eq, vec![one_lvl]);
        let r_ty = self.kernel.const_(self.arith.r, vec![]);
        let e = self.kernel.app(eq, r_ty);
        let e = self.kernel.app(e, x);
        self.kernel.app(e, y)
    }

    /// `Eq.refl R a : Eq R a a`.
    fn eq_refl_r(&mut self, a: ExprId) -> ExprId {
        let one_lvl = {
            let z = self.kernel.level_zero();
            self.kernel.level_succ(z)
        };
        let refl = self.kernel.const_(self.arith.logic.eq_refl, vec![one_lvl]);
        let r_ty = self.kernel.const_(self.arith.r, vec![]);
        let e = self.kernel.app(refl, r_ty);
        self.kernel.app(e, a)
    }

    /// `Eq.rec`-based transport over the `R` carrier: given `h : Eq R p q` and a
    /// `refl_case : motive p (Eq.refl R p)`, builds `motive q h`. Mirrors the EUF
    /// [`ReconstructCtx::mk_eq_rec_transport`] but at the `R` (`Sort 1`) carrier.
    fn eq_rec_transport_r(
        &mut self,
        p: ExprId,
        motive: ExprId,
        refl_case: ExprId,
        q: ExprId,
        h: ExprId,
    ) -> ExprId {
        let z = self.kernel.level_zero();
        let one_lvl = self.kernel.level_succ(z);
        let rec = self
            .kernel
            .const_(self.arith.logic.eq_rec, vec![z, one_lvl]);
        let r_ty = self.kernel.const_(self.arith.r, vec![]);
        let e = self.kernel.app(rec, r_ty);
        let e = self.kernel.app(e, p);
        let e = self.kernel.app(e, motive);
        let e = self.kernel.app(e, refl_case);
        let e = self.kernel.app(e, q);
        self.kernel.app(e, h)
    }

    /// `Eq.symm`: given `h : Eq R a b`, build a proof of `Eq R b a`.
    ///
    /// `Eq.rec R a (fun x _ => Eq R x a) (Eq.refl R a) b h`.
    fn eq_symm_r(&mut self, a: ExprId, b: ExprId, h: ExprId) -> ExprId {
        let motive = {
            let x1 = self.kernel.bvar(1);
            let eq_x_a = self.mk_eq_r(x1, a);
            let x0 = self.kernel.bvar(0);
            let eq_a_x = self.mk_eq_r(a, x0);
            let anon = self.kernel.anon();
            let inner = self.kernel.lam(anon, eq_a_x, eq_x_a, BinderInfo::Default);
            let r_ty = self.kernel.const_(self.arith.r, vec![]);
            self.kernel.lam(anon, r_ty, inner, BinderInfo::Default)
        };
        let refl_case = self.eq_refl_r(a);
        self.eq_rec_transport_r(a, motive, refl_case, b, h)
    }

    /// `Eq.trans`: given `h1 : Eq R a b` and `h2 : Eq R b c`, build `Eq R a c`.
    ///
    /// `Eq.rec R b (fun x _ => Eq R a x) h1 c h2`.
    fn eq_trans_r(&mut self, a: ExprId, b: ExprId, c: ExprId, h1: ExprId, h2: ExprId) -> ExprId {
        let motive = {
            let x1 = self.kernel.bvar(1);
            let eq_a_x = self.mk_eq_r(a, x1);
            let x0 = self.kernel.bvar(0);
            let eq_b_x = self.mk_eq_r(b, x0);
            let anon = self.kernel.anon();
            let inner = self.kernel.lam(anon, eq_b_x, eq_a_x, BinderInfo::Default);
            let r_ty = self.kernel.const_(self.arith.r, vec![]);
            self.kernel.lam(anon, r_ty, inner, BinderInfo::Default)
        };
        self.eq_rec_transport_r(b, motive, h1, c, h2)
    }

    /// Congruence on the *left* argument of `add`: given `h : Eq R a a'`, build
    /// `Eq R (add a b) (add a' b)`.
    fn congr_add_left(&mut self, a: ExprId, ap: ExprId, b: ExprId, h: ExprId) -> ExprId {
        // motive := fun (x : R) (_ : Eq R a x) => Eq R (add a b) (add x b).
        let motive = {
            let a_b = self.mk_add(a, b);
            let x1 = self.kernel.bvar(1);
            let x_b = self.mk_add(x1, b);
            let eq_body = self.mk_eq_r(a_b, x_b);
            let x0 = self.kernel.bvar(0);
            let eq_a_x = self.mk_eq_r(a, x0);
            let anon = self.kernel.anon();
            let inner = self.kernel.lam(anon, eq_a_x, eq_body, BinderInfo::Default);
            let r_ty = self.kernel.const_(self.arith.r, vec![]);
            self.kernel.lam(anon, r_ty, inner, BinderInfo::Default)
        };
        let refl_case = {
            let a_b = self.mk_add(a, b);
            self.eq_refl_r(a_b)
        };
        self.eq_rec_transport_r(a, motive, refl_case, ap, h)
    }

    /// Congruence on the *right* argument of `add`: given `h : Eq R b b'`, build
    /// `Eq R (add a b) (add a b')`.
    fn congr_add_right(&mut self, a: ExprId, b: ExprId, bp: ExprId, h: ExprId) -> ExprId {
        // motive := fun (x : R) (_ : Eq R b x) => Eq R (add a b) (add a x).
        let motive = {
            let a_b = self.mk_add(a, b);
            let x1 = self.kernel.bvar(1);
            let a_x = self.mk_add(a, x1);
            let eq_body = self.mk_eq_r(a_b, a_x);
            let x0 = self.kernel.bvar(0);
            let eq_b_x = self.mk_eq_r(b, x0);
            let anon = self.kernel.anon();
            let inner = self.kernel.lam(anon, eq_b_x, eq_body, BinderInfo::Default);
            let r_ty = self.kernel.const_(self.arith.r, vec![]);
            self.kernel.lam(anon, r_ty, inner, BinderInfo::Default)
        };
        let refl_case = {
            let a_b = self.mk_add(a, b);
            self.eq_refl_r(a_b)
        };
        self.eq_rec_transport_r(b, motive, refl_case, bp, h)
    }

    /// `add_assoc a b c : Eq R (add (add a b) c) (add a (add b c))`.
    fn add_assoc_eq(&mut self, a: ExprId, b: ExprId, c: ExprId) -> ExprId {
        let ax = self.kernel.const_(self.arith.add_assoc, vec![]);
        let e = self.kernel.app(ax, a);
        let e = self.kernel.app(e, b);
        self.kernel.app(e, c)
    }

    /// `add_comm a b : Eq R (add a b) (add b a)`.
    fn add_comm_eq(&mut self, a: ExprId, b: ExprId) -> ExprId {
        let ax = self.kernel.const_(self.arith.add_comm, vec![]);
        let e = self.kernel.app(ax, a);
        self.kernel.app(e, b)
    }

    /// `add_zero a : Eq R (add a zero) a`.
    fn add_zero_eq(&mut self, a: ExprId) -> ExprId {
        let ax = self.kernel.const_(self.arith.add_zero, vec![]);
        self.kernel.app(ax, a)
    }

    /// `add_neg a : Eq R (add a (neg a)) zero`.
    fn add_neg_eq(&mut self, a: ExprId) -> ExprId {
        let ax = self.kernel.const_(self.arith.add_neg, vec![]);
        self.kernel.app(ax, a)
    }

    // -----------------------------------------------------------------------
    // Multiplicative ring layer (degree-2 SOS ring normalizer, ADR-0040).
    //
    // The single-square SOS path needs no ring normalizer (the asserted lhs is
    // literally `ℓ·ℓ`). A *sum-of-monomials* SOS — e.g. AM-GM's
    // `x² + y² − 2xy < 0`, whose lhs is `(x−y)·(x−y)` only after a ring identity —
    // does: we must PROVE `Eq R p ((x−y)·(x−y))` in the kernel and rewrite the
    // square-nonnegativity across it. The helpers below extend the additive
    // `Eq R` engine with the multiplicative axiom wrappers, `mul` congruence, and
    // the three derived `neg`/`mul` bridge lemmas (each grounded in
    // inverse-uniqueness, which is itself derived from the additive axioms — no
    // new kernel axiom is introduced).
    // -----------------------------------------------------------------------

    /// `mul_comm a b : Eq R (mul a b) (mul b a)`.
    fn mul_comm_eq(&mut self, a: ExprId, b: ExprId) -> ExprId {
        let ax = self.kernel.const_(self.arith.mul_comm, vec![]);
        let e = self.kernel.app(ax, a);
        self.kernel.app(e, b)
    }

    /// `mul_zero a : Eq R (mul a zero) zero`.
    fn mul_zero_eq(&mut self, a: ExprId) -> ExprId {
        let ax = self.kernel.const_(self.arith.mul_zero, vec![]);
        self.kernel.app(ax, a)
    }

    /// `left_distrib a b c : Eq R (mul a (add b c)) (add (mul a b) (mul a c))`.
    fn left_distrib_eq(&mut self, a: ExprId, b: ExprId, c: ExprId) -> ExprId {
        let ax = self.kernel.const_(self.arith.left_distrib, vec![]);
        let e = self.kernel.app(ax, a);
        let e = self.kernel.app(e, b);
        self.kernel.app(e, c)
    }

    /// Congruence on the *left* argument of `mul`: given `h : Eq R a a'`, build
    /// `Eq R (mul a b) (mul a' b)`.
    fn congr_mul_left(&mut self, a: ExprId, ap: ExprId, b: ExprId, h: ExprId) -> ExprId {
        // motive := fun (x : R) (_ : Eq R a x) => Eq R (mul a b) (mul x b).
        let motive = {
            let a_b = self.mk_mul(a, b);
            let x1 = self.kernel.bvar(1);
            let x_b = self.mk_mul(x1, b);
            let eq_body = self.mk_eq_r(a_b, x_b);
            let x0 = self.kernel.bvar(0);
            let eq_a_x = self.mk_eq_r(a, x0);
            let anon = self.kernel.anon();
            let inner = self.kernel.lam(anon, eq_a_x, eq_body, BinderInfo::Default);
            let r_ty = self.kernel.const_(self.arith.r, vec![]);
            self.kernel.lam(anon, r_ty, inner, BinderInfo::Default)
        };
        let refl_case = {
            let a_b = self.mk_mul(a, b);
            self.eq_refl_r(a_b)
        };
        self.eq_rec_transport_r(a, motive, refl_case, ap, h)
    }

    /// Congruence on the *right* argument of `mul`: given `h : Eq R b b'`, build
    /// `Eq R (mul a b) (mul a b')`.
    fn congr_mul_right(&mut self, a: ExprId, b: ExprId, bp: ExprId, h: ExprId) -> ExprId {
        // motive := fun (x : R) (_ : Eq R b x) => Eq R (mul a b) (mul a x).
        let motive = {
            let a_b = self.mk_mul(a, b);
            let x1 = self.kernel.bvar(1);
            let a_x = self.mk_mul(a, x1);
            let eq_body = self.mk_eq_r(a_b, a_x);
            let x0 = self.kernel.bvar(0);
            let eq_b_x = self.mk_eq_r(b, x0);
            let anon = self.kernel.anon();
            let inner = self.kernel.lam(anon, eq_b_x, eq_body, BinderInfo::Default);
            let r_ty = self.kernel.const_(self.arith.r, vec![]);
            self.kernel.lam(anon, r_ty, inner, BinderInfo::Default)
        };
        let refl_case = {
            let a_b = self.mk_mul(a, b);
            self.eq_refl_r(a_b)
        };
        self.eq_rec_transport_r(b, motive, refl_case, bp, h)
    }

    /// Inverse-uniqueness over the additive group: from `h1 : Eq R (add c u) zero`
    /// and `h2 : Eq R (add c v) zero`, derive `Eq R u v`. Pure additive-axiom chain
    /// (`add_zero`, `add_assoc`, `add_comm` + congruence), so it needs **no** new
    /// kernel axiom — it is the bridge every `neg`/`mul` lemma below rests on.
    ///
    /// `u = u+0 = u+(c+v) = (u+c)+v = (c+u)+v = 0+v = v+0 = v`.
    fn add_left_cancel_eq(
        &mut self,
        c: ExprId,
        u: ExprId,
        v: ExprId,
        h1: ExprId,
        h2: ExprId,
    ) -> ExprId {
        let zero = self.mk_zero();
        let cv = self.mk_add(c, v);
        let cu = self.mk_add(c, u);
        // s0 : u = add u zero  (symm add_zero).
        let u_zero = self.mk_add(u, zero);
        let s0 = {
            let az = self.add_zero_eq(u); // add u zero = u
            self.eq_symm_r(u_zero, u, az) // u = add u zero
        };
        // s1 : add u zero = add u (add c v)  (congr_right with symm h2).
        let h2_sym = self.eq_symm_r(cv, zero, h2); // zero = add c v
        let s1 = self.congr_add_right(u, zero, cv, h2_sym);
        // s2 : add u (add c v) = add (add u c) v  (symm add_assoc).
        let u_cv = self.mk_add(u, cv);
        let uc = self.mk_add(u, c);
        let uc_v = self.mk_add(uc, v);
        let s2 = {
            let assoc = self.add_assoc_eq(u, c, v); // (u+c)+v = u+(c+v)
            self.eq_symm_r(uc_v, u_cv, assoc) // u+(c+v) = (u+c)+v
        };
        // s3 : add (add u c) v = add (add c u) v  (congr_left add_comm u c).
        let comm_uc = self.add_comm_eq(u, c); // add u c = add c u
        let s3 = self.congr_add_left(uc, cu, v, comm_uc);
        // s4 : add (add c u) v = add zero v  (congr_left h1).
        let cu_v = self.mk_add(cu, v);
        let s4 = self.congr_add_left(cu, zero, v, h1);
        // s5 : add zero v = add v zero  (add_comm zero v).
        let zero_v = self.mk_add(zero, v);
        let v_zero = self.mk_add(v, zero);
        let s5 = self.add_comm_eq(zero, v);
        // s6 : add v zero = v  (add_zero v).
        let s6 = self.add_zero_eq(v);
        // Chain u = … = v.
        let t01 = self.eq_trans_r(u, u_zero, u_cv, s0, s1);
        let t02 = self.eq_trans_r(u, u_cv, uc_v, t01, s2);
        let t03 = self.eq_trans_r(u, uc_v, cu_v, t02, s3);
        let t04 = self.eq_trans_r(u, cu_v, zero_v, t03, s4);
        let t05 = self.eq_trans_r(u, zero_v, v_zero, t04, s5);
        self.eq_trans_r(u, v_zero, v, t05, s6)
    }

    /// `neg_neg z : Eq R (neg (neg z)) z`. Derived: `z` and `neg (neg z)` are both
    /// additive inverses of `neg z`, so inverse-uniqueness identifies them.
    fn neg_neg_eq(&mut self, z: ExprId) -> ExprId {
        let nz = self.mk_neg(z);
        let nnz = self.mk_neg(nz);
        let zero = self.mk_zero();
        // h1 : add (neg z) z = zero  — from add_neg (neg z)? No: add_neg gives
        // `add a (neg a) = zero`. With `a = z`: add z (neg z) = zero; commute.
        let add_z_nz = self.mk_add(z, nz);
        let add_nz_z = self.mk_add(nz, z);
        let h1 = {
            let comm = self.add_comm_eq(nz, z); // add (neg z) z = add z (neg z)
            let an = self.add_neg_eq(z); // add z (neg z) = zero
            self.eq_trans_r(add_nz_z, add_z_nz, zero, comm, an)
        };
        // h2 : add (neg z) (neg (neg z)) = zero  — add_neg (neg z).
        let h2 = self.add_neg_eq(nz);
        // inverse-uniqueness with c = neg z, u = z, v = neg (neg z) ⇒ z = neg(neg z).
        let z_eq_nnz = self.add_left_cancel_eq(nz, z, nnz, h1, h2);
        self.eq_symm_r(z, nnz, z_eq_nnz) // neg (neg z) = z
    }

    /// `mul_neg_right a b : Eq R (mul a (neg b)) (neg (mul a b))`. Derived:
    /// `mul a (neg b)` is an additive inverse of `mul a b` (via `left_distrib` +
    /// `add_neg` + `mul_zero`), and `neg (mul a b)` is too; inverse-uniqueness
    /// identifies them.
    fn mul_neg_right_eq(&mut self, a: ExprId, b: ExprId) -> ExprId {
        let nb = self.mk_neg(b);
        let ab = self.mk_mul(a, b);
        let a_nb = self.mk_mul(a, nb);
        let zero = self.mk_zero();
        // inv1 : add (mul a b) (mul a (neg b)) = zero.
        //   left_distrib a b (neg b) : mul a (add b (neg b)) = add (mul a b)(mul a (neg b))
        //   add_neg b               : add b (neg b) = zero
        //   ⇒ mul a (add b (neg b)) = mul a zero = zero.
        let b_nb = self.mk_add(b, nb);
        let a_bnb = self.mk_mul(a, b_nb);
        let sum = self.mk_add(ab, a_nb);
        let inv1 = {
            let ld = self.left_distrib_eq(a, b, nb); // a*(b+(-b)) = a*b + a*(-b)
            let an = self.add_neg_eq(b); // b+(-b) = zero
            let cong = self.congr_mul_right(a, b_nb, zero, an); // a*(b+(-b)) = a*0
            let mz = self.mul_zero_eq(a); // a*0 = zero
            let a_zero = self.mk_mul(a, zero);
            // a*(b+(-b)) = zero
            let lhs_zero = self.eq_trans_r(a_bnb, a_zero, zero, cong, mz);
            // sum = a*(b+(-b)) (symm ld), then = zero.
            let sum_to_lhs = self.eq_symm_r(a_bnb, sum, ld); // a*b+a*(-b) = a*(b+(-b))
            self.eq_trans_r(sum, a_bnb, zero, sum_to_lhs, lhs_zero)
        };
        // inv2 : add (mul a b) (neg (mul a b)) = zero  — add_neg (mul a b).
        let inv2 = self.add_neg_eq(ab);
        // inverse-uniqueness: c = mul a b, u = mul a (neg b), v = neg (mul a b).
        let neg_ab = self.mk_neg(ab);
        self.add_left_cancel_eq(ab, a_nb, neg_ab, inv1, inv2)
    }

    /// `mul_neg_left a b : Eq R (mul (neg a) b) (neg (mul a b))`. Derived from
    /// `mul_neg_right` by commuting the product on both sides of the `neg`.
    fn mul_neg_left_eq(&mut self, a: ExprId, b: ExprId) -> ExprId {
        let na = self.mk_neg(a);
        let na_b = self.mk_mul(na, b);
        let b_na = self.mk_mul(b, na);
        let ba = self.mk_mul(b, a);
        let ab = self.mk_mul(a, b);
        // mul (neg a) b =[mul_comm] mul b (neg a) =[mul_neg_right] neg (mul b a)
        //   =[congr neg mul_comm] neg (mul a b).
        let comm1 = self.mul_comm_eq(na, b); // (neg a)*b = b*(neg a)
        let mnr = self.mul_neg_right_eq(b, a); // b*(neg a) = neg (b*a)
        let neg_ba = self.mk_neg(ba);
        let comm2 = self.mul_comm_eq(b, a); // b*a = a*b
        let neg_ab = self.mk_neg(ab);
        let neg_cong = self.congr_neg(ba, ab, comm2); // neg (b*a) = neg (a*b)
        let t01 = self.eq_trans_r(na_b, b_na, neg_ba, comm1, mnr);
        self.eq_trans_r(na_b, neg_ba, neg_ab, t01, neg_cong)
    }

    /// Congruence under `neg`: given `h : Eq R a a'`, build `Eq R (neg a) (neg a')`.
    fn congr_neg(&mut self, a: ExprId, ap: ExprId, h: ExprId) -> ExprId {
        // motive := fun (x : R) (_ : Eq R a x) => Eq R (neg a) (neg x).
        let motive = {
            let neg_a = self.mk_neg(a);
            let x1 = self.kernel.bvar(1);
            let neg_x = self.mk_neg(x1);
            let eq_body = self.mk_eq_r(neg_a, neg_x);
            let x0 = self.kernel.bvar(0);
            let eq_a_x = self.mk_eq_r(a, x0);
            let anon = self.kernel.anon();
            let inner = self.kernel.lam(anon, eq_a_x, eq_body, BinderInfo::Default);
            let r_ty = self.kernel.const_(self.arith.r, vec![]);
            self.kernel.lam(anon, r_ty, inner, BinderInfo::Default)
        };
        let refl_case = {
            let neg_a = self.mk_neg(a);
            self.eq_refl_r(neg_a)
        };
        self.eq_rec_transport_r(a, motive, refl_case, ap, h)
    }

    /// `neg_add a b : Eq R (neg (add a b)) (add (neg a) (neg b))`. Derived:
    /// `add (neg a)(neg b)` is an additive inverse of `add a b` (shown by
    /// reassociating `(a+b)+((-a)+(-b))` to `zero`), and `neg (add a b)` is too;
    /// inverse-uniqueness identifies them.
    fn neg_add_eq(&mut self, a: ExprId, b: ExprId) -> ExprId {
        let na = self.mk_neg(a);
        let nb = self.mk_neg(b);
        let ab = self.mk_add(a, b);
        let na_nb = self.mk_add(na, nb); // (-a)+(-b)
        let zero = self.mk_zero();
        // inv1 : add (add a b) (add (neg a)(neg b)) = zero.
        let inv1 = {
            // (a+b)+T =[add_assoc a b T] a+(b+T),  T = (-a)+(-b).
            let assoc0 = self.add_assoc_eq(a, b, na_nb);
            let ab_t = self.mk_add(ab, na_nb); // (a+b)+T
            let b_t = self.mk_add(b, na_nb); // b+T
            let a_bt = self.mk_add(a, b_t); // a+(b+T)
            // inner: b+T = b+((-a)+(-b)) ⟶ -a.
            // b+((-a)+(-b)) =[symm add_assoc b (-a)(-b)] (b+(-a))+(-b)
            let assoc1 = self.add_assoc_eq(b, na, nb); // (b+(-a))+(-b) = b+((-a)+(-b))
            let b_na = self.mk_add(b, na); // b+(-a)
            let bna_nb = self.mk_add(b_na, nb); // (b+(-a))+(-b)
            let s1 = self.eq_symm_r(bna_nb, b_t, assoc1); // b+T = (b+(-a))+(-b)
            // (b+(-a)) =[add_comm] ((-a)+b) ⟶ congr_left.
            let na_b = self.mk_add(na, b); // (-a)+b
            let comm1 = self.add_comm_eq(b, na); // b+(-a) = (-a)+b
            let s2 = self.congr_add_left(b_na, na_b, nb, comm1); // (b+(-a))+(-b) = ((-a)+b)+(-b)
            let nab_nb = self.mk_add(na_b, nb); // ((-a)+b)+(-b)
            // ((-a)+b)+(-b) =[add_assoc (-a) b (-b)] (-a)+(b+(-b)).
            let assoc2 = self.add_assoc_eq(na, b, nb);
            let b_nb = self.mk_add(b, nb); // b+(-b)
            let na_bnb = self.mk_add(na, b_nb); // (-a)+(b+(-b))
            // (b+(-b)) =[add_neg b] zero ⟶ congr_right.
            let an_b = self.add_neg_eq(b); // b+(-b) = zero
            let na_zero = self.mk_add(na, zero); // (-a)+zero
            let s3 = self.congr_add_right(na, b_nb, zero, an_b); // (-a)+(b+(-b)) = (-a)+zero
            // (-a)+zero =[add_zero] -a.
            let s4 = self.add_zero_eq(na); // (-a)+zero = -a
            // chain inner: b+T = (b+(-a))+(-b) = ((-a)+b)+(-b) = (-a)+(b+(-b)) = (-a)+zero = -a.
            let i01 = self.eq_trans_r(b_t, bna_nb, nab_nb, s1, s2);
            let i02 = self.eq_trans_r(b_t, nab_nb, na_bnb, i01, assoc2);
            let i03 = self.eq_trans_r(b_t, na_bnb, na_zero, i02, s3);
            let inner = self.eq_trans_r(b_t, na_zero, na, i03, s4); // b+T = -a
            // a+(b+T) =[congr_right inner] a+(-a) =[add_neg a] zero.
            let a_na = self.mk_add(a, na); // a+(-a)
            let lift = self.congr_add_right(a, b_t, na, inner); // a+(b+T) = a+(-a)
            let an_a = self.add_neg_eq(a); // a+(-a) = zero
            // (a+b)+T = a+(b+T) = a+(-a) = zero.
            let c01 = self.eq_trans_r(ab_t, a_bt, a_na, assoc0, lift);
            self.eq_trans_r(ab_t, a_na, zero, c01, an_a)
        };
        // inv2 : add (add a b) (neg (add a b)) = zero  — add_neg (add a b).
        let inv2 = self.add_neg_eq(ab);
        // inverse-uniqueness: c = add a b, u = add(neg a)(neg b), v = neg(add a b).
        let neg_ab = self.mk_neg(ab);
        let u_eq_v = self.add_left_cancel_eq(ab, na_nb, neg_ab, inv1, inv2); // (-a)+(-b) = neg(a+b)
        self.eq_symm_r(na_nb, neg_ab, u_eq_v) // neg(a+b) = (-a)+(-b)
    }

    /// `neg_mul_neg a b : Eq R (mul (neg a) (neg b)) (mul a b)`. Derived:
    /// `(neg a)·(neg b) = neg ((neg a)·b) = neg (neg (a·b)) = a·b`.
    fn neg_mul_neg_eq(&mut self, a: ExprId, b: ExprId) -> ExprId {
        let na = self.mk_neg(a);
        let nb = self.mk_neg(b);
        let na_nb = self.mk_mul(na, nb);
        let na_b = self.mk_mul(na, b);
        let ab = self.mk_mul(a, b);
        // (neg a)*(neg b) =[mul_neg_right (neg a) b] neg ((neg a)*b)
        let mnr = self.mul_neg_right_eq(na, b); // (neg a)*(neg b) = neg ((neg a)*b)
        let neg_na_b = self.mk_neg(na_b);
        // neg ((neg a)*b) =[congr_neg mul_neg_left a b] neg (neg (a*b))
        let mnl = self.mul_neg_left_eq(a, b); // (neg a)*b = neg (a*b)
        let neg_ab = self.mk_neg(ab);
        let neg_neg_ab = self.mk_neg(neg_ab);
        let cong = self.congr_neg(na_b, neg_ab, mnl); // neg ((neg a)*b) = neg (neg (a*b))
        // neg (neg (a*b)) =[neg_neg] a*b
        let nn = self.neg_neg_eq(ab); // neg (neg (a*b)) = a*b
        let t01 = self.eq_trans_r(na_nb, neg_na_b, neg_neg_ab, mnr, cong);
        self.eq_trans_r(na_nb, neg_neg_ab, ab, t01, nn)
    }
}

/// A signed unit **generator** in the canonical additive normal form: either a
/// bare variable `±xⱼ` or the unit `±1`. The canonical form of a linear expression
/// is a right-nested `add` over a flat list of generators (terminated by `zero`),
/// with variables ascending by index and the constant last. Repeated generators
/// model integer coefficients (`coeff = 3` ⇒ three `+xⱼ` generators).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Gen {
    /// `+xⱼ` (variable at dense index).
    Var(usize),
    /// `-xⱼ`.
    NegVar(usize),
    /// `+one`.
    One,
    /// `-one` (= `neg one`).
    NegOne,
}

impl Gen {
    /// The negation of this generator (so `Var` ↔ `NegVar`, `One` ↔ `NegOne`).
    fn negate(self) -> Self {
        match self {
            Gen::Var(i) => Gen::NegVar(i),
            Gen::NegVar(i) => Gen::Var(i),
            Gen::One => Gen::NegOne,
            Gen::NegOne => Gen::One,
        }
    }

    /// A total sort key putting variables (ascending by index, `+` before `−`)
    /// ahead of the constant generators. The exact order only needs to be total
    /// and to keep a generator adjacent to its negation after bubbling, so the
    /// merge can cancel; this key does both.
    fn sort_key(self) -> (usize, u8) {
        match self {
            Gen::Var(i) => (i, 0),
            Gen::NegVar(i) => (i, 1),
            Gen::One => (usize::MAX, 0),
            Gen::NegOne => (usize::MAX, 1),
        }
    }
}

/// A **monomial** of total degree ≤ 2 over canonical variable indices, the atom of
/// the degree-2 ring normalizer's canonical form (ADR-0040 generalization). Its
/// kernel encoding is a fixed, deterministic `R`-expression:
/// - [`Mono::Const`] → `one`,
/// - [`Mono::Lin`] → `xᵢ`,
/// - [`Mono::Quad`] (`i ≤ j`) → `mul xᵢ xⱼ`.
///
/// `Quad` is normalized so `i ≤ j`, giving each unordered variable pair a single
/// canonical kernel representative (`x·y` and `y·x` map to the same `Quad`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Mono {
    /// The constant monomial `1`.
    Const,
    /// The linear monomial `xᵢ`.
    Lin(usize),
    /// The quadratic monomial `xᵢ·xⱼ` with `i ≤ j` (the kernel term is `mul xᵢ xⱼ`).
    Quad(usize, usize),
}

impl Mono {
    /// Build the canonical quadratic monomial for an unordered variable pair,
    /// ordering the two indices so the kernel representative is unique.
    fn quad(i: usize, j: usize) -> Self {
        if i <= j {
            Mono::Quad(i, j)
        } else {
            Mono::Quad(j, i)
        }
    }

    /// A total sort key: linear monomials (ascending index) first, then quadratic
    /// monomials (lexicographic on the ordered pair), then the constant last —
    /// mirroring [`Gen::sort_key`]'s "variables before constant" convention. Only
    /// totality and determinism matter (it fixes the canonical order).
    fn sort_key(self) -> (u8, usize, usize) {
        match self {
            Mono::Lin(i) => (0, i, 0),
            Mono::Quad(i, j) => (1, i, j),
            Mono::Const => (2, usize::MAX, usize::MAX),
        }
    }
}

/// A signed monomial **generator** in the degree-2 canonical additive normal form:
/// a [`Mono`] with a sign. The canonical form of a degree-≤2 expression is a
/// right-nested `add` over a flat list of these (terminated by `zero`), monomials
/// in [`Mono::sort_key`] order, repeated to model integer coefficients. This is the
/// degree-2 analogue of [`Gen`]; the normalizer reuses the same bubble-sort +
/// cancellation algorithm, extended with a multiplicative distribution step.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct MonoGen {
    mono: Mono,
    /// `true` ⇒ the generator is `neg (mono_expr)`, `false` ⇒ `mono_expr`.
    neg: bool,
}

impl MonoGen {
    fn pos(mono: Mono) -> Self {
        MonoGen { mono, neg: false }
    }

    /// The negation of this generator (flips the sign bit).
    fn negate(self) -> Self {
        MonoGen {
            mono: self.mono,
            neg: !self.neg,
        }
    }

    /// A total sort key keeping a generator adjacent to its negation after bubbling
    /// (same monomial ⇒ same primary key; sign breaks the tie) so the merge can
    /// cancel — exactly as [`Gen::sort_key`] does for the linear engine.
    fn sort_key(self) -> (u8, usize, usize, u8) {
        let (a, b, c) = self.mono.sort_key();
        (a, b, c, u8::from(self.neg))
    }
}

/// A small owned degree-≤2 expression AST over canonical variable indices, the
/// **input** to the degree-2 ring normalizer ([`LraReconstructCtx::normalize_deg2`]).
/// Built from `var`/`neg`/`add`/`mul`; the normalizer both emits its faithful kernel
/// `R`-encoding and proves it equals the canonical signed-monomial sum.
#[derive(Debug, Clone)]
enum RExpr {
    /// The variable `xᵢ`.
    Var(usize),
    /// `neg e`.
    Neg(Box<RExpr>),
    /// `add a b`.
    Add(Box<RExpr>, Box<RExpr>),
    /// `mul a b`.
    Mul(Box<RExpr>, Box<RExpr>),
    /// The constant `one`.
    One,
}

/// The carrier of the general-Farkas additive ring engine, on top of
/// [`LraReconstructCtx`]. Builds generator expressions, the canonical right-nested
/// normal form, and the per-rewrite `Eq R` proofs that drive normalization.
#[allow(dead_code)]
impl LraReconstructCtx {
    /// The `R` expression for a single generator.
    fn gen_expr(&mut self, g: Gen) -> ExprId {
        match g {
            Gen::Var(i) => {
                let name = self.var_const(i);
                self.kernel.const_(name, vec![])
            }
            Gen::NegVar(i) => {
                let name = self.var_const(i);
                let v = self.kernel.const_(name, vec![]);
                self.mk_neg(v)
            }
            Gen::One => self.mk_one(),
            Gen::NegOne => {
                let one = self.mk_one();
                self.mk_neg(one)
            }
        }
    }

    /// The canonical right-nested additive expression `g0 + (g1 + … + (g_{k-1} + zero))`
    /// over `gens`; an empty list is `zero`.
    fn gens_to_expr(&mut self, gens: &[Gen]) -> ExprId {
        let mut acc = self.mk_zero();
        for &g in gens.iter().rev() {
            let ge = self.gen_expr(g);
            acc = self.mk_add(ge, acc);
        }
        acc
    }

    /// Lift a tail rewrite `tail_proof : Eq R tail tail'` up through the `prefix`
    /// leading generators, yielding `Eq R (prefix ++ tail) (prefix ++ tail')` where
    /// both sides are the right-nested canonical forms. Each leading generator is
    /// re-attached with [`Self::congr_add_right`].
    fn lift_tail_rewrite(
        &mut self,
        prefix: &[Gen],
        tail: &[Gen],
        tail2: &[Gen],
        mut proof: ExprId,
    ) -> ExprId {
        // Build proof bottom-up: at each step we have `proof : Eq R T T2` for the
        // current tail `T = (prefix[i+1..] ++ tail)`; prepend prefix[i].
        for k in (0..prefix.len()).rev() {
            let g = self.gen_expr(prefix[k]);
            let mut sub_tail: Vec<Gen> = prefix[k + 1..].to_vec();
            sub_tail.extend_from_slice(tail);
            let mut sub_tail2: Vec<Gen> = prefix[k + 1..].to_vec();
            sub_tail2.extend_from_slice(tail2);
            let t = self.gens_to_expr(&sub_tail);
            let t2 = self.gens_to_expr(&sub_tail2);
            proof = self.congr_add_right(g, t, t2, proof);
        }
        proof
    }

    /// Prove `Eq R (g0 + (g1 + tail)) (g1 + (g0 + tail))` — an adjacent swap at the
    /// head of a right-nested sum. `t` is the canonical expr of `tail`.
    fn swap_head_eq(&mut self, g0: Gen, g1: Gen, tail: &[Gen]) -> ExprId {
        let e0 = self.gen_expr(g0);
        let e1 = self.gen_expr(g1);
        let t = self.gens_to_expr(tail);
        // add e0 (add e1 t) =[symm assoc] add (add e0 e1) t
        let assoc1 = self.add_assoc_eq(e0, e1, t); // (e0+e1)+t = e0+(e1+t)
        let lhs = {
            let inner = self.mk_add(e1, t);
            self.mk_add(e0, inner)
        };
        let mid1 = {
            let inner = self.mk_add(e0, e1);
            self.mk_add(inner, t)
        };
        let step1 = self.eq_symm_r(mid1, lhs, assoc1); // add e0 (add e1 t) = add (add e0 e1) t
        // congr_left (add_comm e0 e1) : add (add e0 e1) t = add (add e1 e0) t
        let comm = self.add_comm_eq(e0, e1); // add e0 e1 = add e1 e0
        let e0e1 = self.mk_add(e0, e1);
        let e1e0 = self.mk_add(e1, e0);
        let step2 = self.congr_add_left(e0e1, e1e0, t, comm);
        // assoc : add (add e1 e0) t = add e1 (add e0 t)
        let step3 = self.add_assoc_eq(e1, e0, t);
        // chain: lhs = mid1 = mid2 = rhs
        let mid2 = self.mk_add(e1e0, t);
        let rhs = {
            let inner = self.mk_add(e0, t);
            self.mk_add(e1, inner)
        };
        let t01 = self.eq_trans_r(lhs, mid1, mid2, step1, step2);
        self.eq_trans_r(lhs, mid2, rhs, t01, step3)
    }

    /// Prove `Eq R (g + (g.negate() + tail)) tail` — cancel an adjacent
    /// generator/anti-generator pair at the head. `t` is the canonical expr of `tail`.
    fn cancel_head_eq(&mut self, g: Gen, tail: &[Gen]) -> ExprId {
        let gn = g.negate();
        let e = self.gen_expr(g);
        let en = self.gen_expr(gn);
        let t = self.gens_to_expr(tail);
        // add e (add en t) =[symm assoc] add (add e en) t
        let assoc = self.add_assoc_eq(e, en, t);
        let lhs = {
            let inner = self.mk_add(en, t);
            self.mk_add(e, inner)
        };
        let mid1 = {
            let inner = self.mk_add(e, en);
            self.mk_add(inner, t)
        };
        let step1 = self.eq_symm_r(mid1, lhs, assoc);
        // Prove `add e en = zero`. add_neg gives `add p (neg p) = zero`. For a
        // `+`-generator g (e = p, en = neg p) this is direct; for a `−`-generator
        // (e = neg p, en = p) commute first.
        let (e_e_en_zero, e_en) = match g {
            Gen::Var(_) | Gen::One => {
                // e = p, en = neg p  ⇒ add_neg p.
                let p = e;
                let an = self.add_neg_eq(p); // add p (neg p) = zero
                let e_en = self.mk_add(e, en);
                (an, e_en)
            }
            Gen::NegVar(_) | Gen::NegOne => {
                // e = neg p, en = p ⇒ add (neg p) p = zero via comm + add_neg.
                let p = en; // the positive form
                let np = e; // neg p
                // add (neg p) p =[comm] add p (neg p) =[add_neg] zero.
                let comm = self.add_comm_eq(np, p); // add np p = add p np
                let an = self.add_neg_eq(p); // add p np = zero
                let lhs_c = self.mk_add(np, p);
                let mid_c = self.mk_add(p, np);
                let zero = self.mk_zero();
                let chained = self.eq_trans_r(lhs_c, mid_c, zero, comm, an);
                let e_en = self.mk_add(e, en);
                (chained, e_en)
            }
        };
        // congr_left (add e en = zero) : add (add e en) t = add zero t
        let zero = self.mk_zero();
        let step2 = self.congr_add_left(e_en, zero, t, e_e_en_zero);
        // add zero t =[comm] add t zero =[add_zero] t
        let comm0 = self.add_comm_eq(zero, t); // add zero t = add t zero
        let addz = self.add_zero_eq(t); // add t zero = t
        let zt = self.mk_add(zero, t);
        let tz = self.mk_add(t, zero);
        let step3 = self.eq_trans_r(zt, tz, t, comm0, addz);
        // chain lhs = mid1 = (add zero t) = t
        let t01 = self.eq_trans_r(lhs, mid1, zt, step1, step2);
        self.eq_trans_r(lhs, zt, t, t01, step3)
    }

    /// Normalize a generator list to the canonical sorted-and-cancelled list,
    /// returning the canonical generators and a proof
    /// `Eq R (gens_to_expr gens) (gens_to_expr canonical)`.
    ///
    /// Implemented as a bubble pass with cancellation: repeatedly find the first
    /// adjacent pair that is either out of sort order (swap) or a cancelling
    /// generator/anti-generator pair (cancel), apply the corresponding head rewrite
    /// lifted to that position, and post-compose into the running proof. Terminates
    /// because every swap strictly decreases the inversion count and every cancel
    /// strictly decreases the length.
    fn normalize_gens(&mut self, gens: &[Gen]) -> (Vec<Gen>, ExprId) {
        let mut cur: Vec<Gen> = gens.to_vec();
        let start = self.gens_to_expr(&cur);
        // proof : Eq R start (gens_to_expr cur), initially refl.
        let mut proof = self.eq_refl_r(start);
        loop {
            // Find first actionable adjacent pair.
            let mut action: Option<(usize, bool)> = None; // (index, is_cancel)
            for i in 0..cur.len().saturating_sub(1) {
                if cur[i].negate() == cur[i + 1] {
                    action = Some((i, true));
                    break;
                }
                if cur[i].sort_key() > cur[i + 1].sort_key() {
                    action = Some((i, false));
                    break;
                }
            }
            let Some((i, is_cancel)) = action else {
                break;
            };
            let prefix = cur[..i].to_vec();
            let before = self.gens_to_expr(&cur);
            if is_cancel {
                let g = cur[i];
                let tail = cur[i + 2..].to_vec();
                let head_proof = self.cancel_head_eq(g, &tail);
                // tail of the lifted rewrite: [g, g.negate()] ++ tail → tail.
                let mut from_tail = vec![g, g.negate()];
                from_tail.extend_from_slice(&tail);
                let lifted = self.lift_tail_rewrite(&prefix, &from_tail, &tail, head_proof);
                let mut next = prefix.clone();
                next.extend_from_slice(&tail);
                let after = self.gens_to_expr(&next);
                proof = self.eq_trans_r(start, before, after, proof, lifted);
                cur = next;
            } else {
                let g0 = cur[i];
                let g1 = cur[i + 1];
                let tail = cur[i + 2..].to_vec();
                let head_proof = self.swap_head_eq(g0, g1, &tail);
                let mut from_tail = vec![g0, g1];
                from_tail.extend_from_slice(&tail);
                let mut to_tail = vec![g1, g0];
                to_tail.extend_from_slice(&tail);
                let lifted = self.lift_tail_rewrite(&prefix, &from_tail, &to_tail, head_proof);
                let mut next = prefix.clone();
                next.push(g1);
                next.push(g0);
                next.extend_from_slice(&tail);
                let after = self.gens_to_expr(&next);
                proof = self.eq_trans_r(start, before, after, proof, lifted);
                cur = next;
            }
        }
        (cur, proof)
    }

    /// Prove `Eq R (add canonA canonB) (gens_to_expr(gensA ++ gensB))` where
    /// `canonA`/`canonB` are the canonical exprs of `gensA`/`gensB`. This "absorbs"
    /// the trailing `zero` of `canonA`, splicing `canonB` in its place, by induction
    /// over `gensA` with `add_assoc` (and `add_comm`+`add_zero` at the base).
    fn append_eq(&mut self, gens_a: &[Gen], gens_b: &[Gen]) -> ExprId {
        let canon_b = self.gens_to_expr(gens_b);
        if gens_a.is_empty() {
            // add zero canon_b =[comm] add canon_b zero =[add_zero] canon_b.
            let zero = self.mk_zero();
            let comm = self.add_comm_eq(zero, canon_b);
            let addz = self.add_zero_eq(canon_b);
            let zt = self.mk_add(zero, canon_b);
            let tz = self.mk_add(canon_b, zero);
            return self.eq_trans_r(zt, tz, canon_b, comm, addz);
        }
        // gens_a = g :: rest. canonA = add g canonRest.
        // add (add g canonRest) canon_b =[assoc] add g (add canonRest canon_b)
        //   =[congr_right (append_eq rest gens_b)] add g (gens_to_expr(rest++gens_b)).
        let g = self.gen_expr(gens_a[0]);
        let rest = &gens_a[1..].to_vec();
        let canon_rest = self.gens_to_expr(rest);
        let assoc = self.add_assoc_eq(g, canon_rest, canon_b);
        let lhs = {
            let ca = self.mk_add(g, canon_rest);
            self.mk_add(ca, canon_b)
        };
        let mid = {
            let inner = self.mk_add(canon_rest, canon_b);
            self.mk_add(g, inner)
        };
        // recursive: add canonRest canon_b = gens_to_expr(rest ++ gens_b)
        let rec = self.append_eq(rest, gens_b);
        let mut rest_b: Vec<Gen> = rest.clone();
        rest_b.extend_from_slice(gens_b);
        let rest_b_expr = self.gens_to_expr(&rest_b);
        let inner_from = self.mk_add(canon_rest, canon_b);
        let step2 = self.congr_add_right(g, inner_from, rest_b_expr, rec);
        let rhs = self.mk_add(g, rest_b_expr);
        self.eq_trans_r(lhs, mid, rhs, assoc, step2)
    }

    // -----------------------------------------------------------------------
    // Degree-2 ring normalizer (ADR-0040 generalization): canonicalize any
    // degree-≤2 `R`-expression built from `var`/`neg`/`add`/`mul`/`one` into a
    // fixed-order sum of signed monomials, carrying an `Eq R` proof. Reuses the
    // additive bubble-sort+cancel engine above, lifted from linear [`Gen`]s to
    // degree-2 [`MonoGen`]s, plus a multiplicative distribution step. No new kernel
    // axiom: every rewrite is one of `left_distrib`/`mul_comm`/`mul_zero`/`mul_one`
    // /the derived neg-bridge lemmas/`add_*` + congruence.
    // -----------------------------------------------------------------------

    /// The kernel `R`-expression for a single bare [`Mono`] (no sign).
    fn mono_expr(&mut self, m: Mono) -> ExprId {
        match m {
            Mono::Const => self.mk_one(),
            Mono::Lin(i) => {
                let name = self.var_const(i);
                self.kernel.const_(name, vec![])
            }
            Mono::Quad(i, j) => {
                let ni = self.var_const(i);
                let xi = self.kernel.const_(ni, vec![]);
                let nj = self.var_const(j);
                let xj = self.kernel.const_(nj, vec![]);
                self.mk_mul(xi, xj)
            }
        }
    }

    /// The kernel `R`-expression for a single signed [`MonoGen`].
    fn mono_gen_expr(&mut self, g: MonoGen) -> ExprId {
        let m = self.mono_expr(g.mono);
        if g.neg { self.mk_neg(m) } else { m }
    }

    /// The canonical right-nested additive expression
    /// `g0 + (g1 + … + (g_{k-1} + zero))` over `gens`; empty ⇒ `zero`.
    fn mono_gens_to_expr(&mut self, gens: &[MonoGen]) -> ExprId {
        let mut acc = self.mk_zero();
        for &g in gens.iter().rev() {
            let ge = self.mono_gen_expr(g);
            acc = self.mk_add(ge, acc);
        }
        acc
    }

    /// Lift a tail rewrite `proof : Eq R tail tail'` up through the `prefix` leading
    /// generators (re-attaching each with [`Self::congr_add_right`]). Degree-2
    /// analogue of [`Self::lift_tail_rewrite`].
    fn mono_lift_tail_rewrite(
        &mut self,
        prefix: &[MonoGen],
        tail: &[MonoGen],
        tail2: &[MonoGen],
        mut proof: ExprId,
    ) -> ExprId {
        for k in (0..prefix.len()).rev() {
            let g = self.mono_gen_expr(prefix[k]);
            let mut sub_tail: Vec<MonoGen> = prefix[k + 1..].to_vec();
            sub_tail.extend_from_slice(tail);
            let mut sub_tail2: Vec<MonoGen> = prefix[k + 1..].to_vec();
            sub_tail2.extend_from_slice(tail2);
            let t = self.mono_gens_to_expr(&sub_tail);
            let t2 = self.mono_gens_to_expr(&sub_tail2);
            proof = self.congr_add_right(g, t, t2, proof);
        }
        proof
    }

    /// Prove `Eq R (g0 + (g1 + tail)) (g1 + (g0 + tail))` — an adjacent head swap.
    /// Degree-2 analogue of [`Self::swap_head_eq`] (identical additive proof shape).
    fn mono_swap_head_eq(&mut self, g0: MonoGen, g1: MonoGen, tail: &[MonoGen]) -> ExprId {
        let e0 = self.mono_gen_expr(g0);
        let e1 = self.mono_gen_expr(g1);
        let t = self.mono_gens_to_expr(tail);
        let assoc1 = self.add_assoc_eq(e0, e1, t);
        let lhs = {
            let inner = self.mk_add(e1, t);
            self.mk_add(e0, inner)
        };
        let mid1 = {
            let inner = self.mk_add(e0, e1);
            self.mk_add(inner, t)
        };
        let step1 = self.eq_symm_r(mid1, lhs, assoc1);
        let comm = self.add_comm_eq(e0, e1);
        let e0e1 = self.mk_add(e0, e1);
        let e1e0 = self.mk_add(e1, e0);
        let step2 = self.congr_add_left(e0e1, e1e0, t, comm);
        let step3 = self.add_assoc_eq(e1, e0, t);
        let mid2 = self.mk_add(e1e0, t);
        let rhs = {
            let inner = self.mk_add(e0, t);
            self.mk_add(e1, inner)
        };
        let t01 = self.eq_trans_r(lhs, mid1, mid2, step1, step2);
        self.eq_trans_r(lhs, mid2, rhs, t01, step3)
    }

    /// Prove `Eq R (g + (g.negate() + tail)) tail` — cancel an adjacent
    /// generator/anti-generator pair at the head. Degree-2 analogue of
    /// [`Self::cancel_head_eq`].
    fn mono_cancel_head_eq(&mut self, g: MonoGen, tail: &[MonoGen]) -> ExprId {
        let gn = g.negate();
        let e = self.mono_gen_expr(g);
        let en = self.mono_gen_expr(gn);
        let t = self.mono_gens_to_expr(tail);
        let assoc = self.add_assoc_eq(e, en, t);
        let lhs = {
            let inner = self.mk_add(en, t);
            self.mk_add(e, inner)
        };
        let mid1 = {
            let inner = self.mk_add(e, en);
            self.mk_add(inner, t)
        };
        let step1 = self.eq_symm_r(mid1, lhs, assoc);
        // Prove `add e en = zero`. For a positive generator (e = p, en = neg p) this
        // is `add_neg p` directly; for a negative one (e = neg p, en = p) commute.
        let e_en = self.mk_add(e, en);
        let e_e_en_zero = if g.neg {
            // e = neg p, en = p ⇒ add (neg p) p = zero via comm + add_neg.
            let p = en;
            let np = e;
            let comm = self.add_comm_eq(np, p);
            let an = self.add_neg_eq(p);
            let lhs_c = self.mk_add(np, p);
            let mid_c = self.mk_add(p, np);
            let zero = self.mk_zero();
            self.eq_trans_r(lhs_c, mid_c, zero, comm, an)
        } else {
            // e = p, en = neg p ⇒ add_neg p.
            self.add_neg_eq(e)
        };
        let zero = self.mk_zero();
        let step2 = self.congr_add_left(e_en, zero, t, e_e_en_zero);
        let comm0 = self.add_comm_eq(zero, t);
        let addz = self.add_zero_eq(t);
        let zt = self.mk_add(zero, t);
        let tz = self.mk_add(t, zero);
        let step3 = self.eq_trans_r(zt, tz, t, comm0, addz);
        let t01 = self.eq_trans_r(lhs, mid1, zt, step1, step2);
        self.eq_trans_r(lhs, zt, t, t01, step3)
    }

    /// Normalize a [`MonoGen`] list to the canonical sorted-and-cancelled list,
    /// returning the canonical generators and a proof
    /// `Eq R (mono_gens_to_expr gens) (mono_gens_to_expr canonical)`. Degree-2
    /// analogue of [`Self::normalize_gens`] (same terminating bubble pass: each
    /// swap strictly decreases the inversion count, each cancel the length).
    fn mono_normalize_gens(&mut self, gens: &[MonoGen]) -> (Vec<MonoGen>, ExprId) {
        let mut cur: Vec<MonoGen> = gens.to_vec();
        let start = self.mono_gens_to_expr(&cur);
        let mut proof = self.eq_refl_r(start);
        loop {
            let mut action: Option<(usize, bool)> = None;
            for i in 0..cur.len().saturating_sub(1) {
                if cur[i].negate() == cur[i + 1] {
                    action = Some((i, true));
                    break;
                }
                if cur[i].sort_key() > cur[i + 1].sort_key() {
                    action = Some((i, false));
                    break;
                }
            }
            let Some((i, is_cancel)) = action else {
                break;
            };
            let prefix = cur[..i].to_vec();
            let before = self.mono_gens_to_expr(&cur);
            if is_cancel {
                let g = cur[i];
                let tail = cur[i + 2..].to_vec();
                let head_proof = self.mono_cancel_head_eq(g, &tail);
                let mut from_tail = vec![g, g.negate()];
                from_tail.extend_from_slice(&tail);
                let lifted = self.mono_lift_tail_rewrite(&prefix, &from_tail, &tail, head_proof);
                let mut next = prefix.clone();
                next.extend_from_slice(&tail);
                let after = self.mono_gens_to_expr(&next);
                proof = self.eq_trans_r(start, before, after, proof, lifted);
                cur = next;
            } else {
                let g0 = cur[i];
                let g1 = cur[i + 1];
                let tail = cur[i + 2..].to_vec();
                let head_proof = self.mono_swap_head_eq(g0, g1, &tail);
                let mut from_tail = vec![g0, g1];
                from_tail.extend_from_slice(&tail);
                let mut to_tail = vec![g1, g0];
                to_tail.extend_from_slice(&tail);
                let lifted = self.mono_lift_tail_rewrite(&prefix, &from_tail, &to_tail, head_proof);
                let mut next = prefix.clone();
                next.push(g1);
                next.push(g0);
                next.extend_from_slice(&tail);
                let after = self.mono_gens_to_expr(&next);
                proof = self.eq_trans_r(start, before, after, proof, lifted);
                cur = next;
            }
        }
        (cur, proof)
    }

    /// Prove `Eq R (add canonA canonB) (mono_gens_to_expr(gensA ++ gensB))` — splice
    /// `canonB` into `canonA`'s trailing `zero`. Degree-2 analogue of
    /// [`Self::append_eq`].
    fn mono_append_eq(&mut self, gens_a: &[MonoGen], gens_b: &[MonoGen]) -> ExprId {
        let canon_b = self.mono_gens_to_expr(gens_b);
        if gens_a.is_empty() {
            let zero = self.mk_zero();
            let comm = self.add_comm_eq(zero, canon_b);
            let addz = self.add_zero_eq(canon_b);
            let zt = self.mk_add(zero, canon_b);
            let tz = self.mk_add(canon_b, zero);
            return self.eq_trans_r(zt, tz, canon_b, comm, addz);
        }
        let g = self.mono_gen_expr(gens_a[0]);
        let rest = gens_a[1..].to_vec();
        let canon_rest = self.mono_gens_to_expr(&rest);
        let assoc = self.add_assoc_eq(g, canon_rest, canon_b);
        let lhs = {
            let ca = self.mk_add(g, canon_rest);
            self.mk_add(ca, canon_b)
        };
        let mid = {
            let inner = self.mk_add(canon_rest, canon_b);
            self.mk_add(g, inner)
        };
        let rec = self.mono_append_eq(&rest, gens_b);
        let mut rest_b: Vec<MonoGen> = rest.clone();
        rest_b.extend_from_slice(gens_b);
        let rest_b_expr = self.mono_gens_to_expr(&rest_b);
        let inner_from = self.mk_add(canon_rest, canon_b);
        let step2 = self.congr_add_right(g, inner_from, rest_b_expr, rec);
        let rhs = self.mk_add(g, rest_b_expr);
        self.eq_trans_r(lhs, mid, rhs, assoc, step2)
    }

    /// Prove `Eq R (neg (mono_gens_to_expr gens)) (mono_gens_to_expr neg_gens)` where
    /// `neg_gens` is `gens` with every generator's sign flipped — `neg` distributes
    /// over the right-nested sum (via `neg_add` + `neg_neg`). Used by the `Neg` case
    /// of [`Self::normalize_deg2`].
    fn mono_neg_gens_eq(&mut self, gens: &[MonoGen]) -> ExprId {
        let inner = self.mono_gens_to_expr(gens);
        let neg_inner = self.mk_neg(inner);
        let Some((&head, tail)) = gens.split_first() else {
            // neg zero = zero (= mono_gens_to_expr []). Derive: zero is its own
            // additive inverse, so neg zero = zero by inverse-uniqueness; but more
            // directly, neg zero = neg (add zero zero)? Use add_zero on neg side:
            // neg zero =[symm add_zero (neg zero)] add (neg zero) zero ... simpler:
            // add zero (neg zero) = zero (add_neg zero) and add zero (neg zero)
            // =[add_comm] add (neg zero) zero =[add_zero] neg zero ⇒ neg zero = zero.
            let zero = self.mk_zero();
            let nz = self.mk_neg(zero);
            let an = self.add_neg_eq(zero); // add zero (neg zero) = zero
            let z_nz = self.mk_add(zero, nz);
            let comm = self.add_comm_eq(zero, nz); // add zero (neg zero) = add (neg zero) zero
            let nz_z = self.mk_add(nz, zero);
            let addz = self.add_zero_eq(nz); // add (neg zero) zero = neg zero
            // neg zero = add (neg zero) zero = add zero (neg zero) = zero.
            let s0 = self.eq_symm_r(nz_z, nz, addz); // neg zero = add (neg zero) zero
            let comm_sym = self.eq_symm_r(z_nz, nz_z, comm); // add (neg zero) zero = add zero (neg zero)
            let t01 = self.eq_trans_r(nz, nz_z, z_nz, s0, comm_sym);
            return self.eq_trans_r(nz, z_nz, zero, t01, an);
        };
        // gens = head :: tail. inner = add (mono_gen_expr head) canon_tail.
        let head_e = self.mono_gen_expr(head);
        let canon_tail = self.mono_gens_to_expr(tail);
        // neg (add head canon_tail) =[neg_add] add (neg head)(neg canon_tail).
        let na = self.neg_add_eq(head_e, canon_tail);
        let neg_head = self.mk_neg(head_e);
        let neg_tail = self.mk_neg(canon_tail);
        let na_nt = self.mk_add(neg_head, neg_tail);
        // (neg head) ⟶ mono_gen_expr(head.negate()):
        //   • head positive (e = p): neg p IS mono_gen_expr(neg) — refl.
        //   • head negative (e = neg p): neg (neg p) =[neg_neg] p = mono_gen_expr(neg).
        let head_neg_gen = head.negate();
        let head_neg_e = self.mono_gen_expr(head_neg_gen);
        let neg_head_eq = if head.neg {
            // head_e = neg p, head_neg_e = p ; neg head_e = neg (neg p) = p.
            self.neg_neg_eq(head_neg_e) // neg (neg p) = p
        } else {
            // neg head_e is literally mono_gen_expr(head.negate()).
            self.eq_refl_r(neg_head)
        };
        // (neg canon_tail) ⟶ mono_gens_to_expr(neg tail) by recursion.
        let rec = self.mono_neg_gens_eq(tail);
        let neg_tail_gens: Vec<MonoGen> = tail.iter().map(|g| g.negate()).collect();
        let neg_tail_canon = self.mono_gens_to_expr(&neg_tail_gens);
        // congr both sides of `add (neg head)(neg canon_tail)`.
        let cong_l = self.congr_add_left(neg_head, head_neg_e, neg_tail, neg_head_eq);
        let mid = self.mk_add(head_neg_e, neg_tail);
        let cong_r = self.congr_add_right(head_neg_e, neg_tail, neg_tail_canon, rec);
        let target = self.mk_add(head_neg_e, neg_tail_canon);
        let cong = self.eq_trans_r(na_nt, mid, target, cong_l, cong_r);
        // neg inner = add(neg head)(neg canon_tail) = target = mono_gens_to_expr(neg gens).
        self.eq_trans_r(neg_inner, na_nt, target, na, cong)
    }

    /// Multiply a single signed generator `g` (LHS, degree-≤1) into a generator list
    /// `bs` (degree-≤1): prove
    /// `Eq R (mul (mono_gen_expr g) (mono_gens_to_expr bs)) (mono_gens_to_expr out)`
    /// where `out[k] = product_gen(g, bs[k])`. Distributes with `left_distrib`,
    /// reducing each `mul (mono_gen_expr g)(mono_gen_expr bs[k])` to a single signed
    /// monomial via [`Self::mul_mono_gen_eq`]. Returns `None` if any product exceeds
    /// degree 2 (out of scope — decline).
    fn mul_gen_into_list_eq(
        &mut self,
        g: MonoGen,
        bs: &[MonoGen],
    ) -> Option<(Vec<MonoGen>, ExprId)> {
        let ge = self.mono_gen_expr(g);
        let bs_canon = self.mono_gens_to_expr(bs);
        let lhs = self.mk_mul(ge, bs_canon);
        let Some((&b0, rest)) = bs.split_first() else {
            // mul ge zero = zero (= mono_gens_to_expr []).
            let mz = self.mul_zero_eq(ge); // mul ge zero = zero
            return Some((Vec::new(), mz));
        };
        // mul ge (add b0e rest_canon) =[left_distrib] add (mul ge b0e)(mul ge rest_canon).
        let b0e = self.mono_gen_expr(b0);
        let rest_canon = self.mono_gens_to_expr(rest);
        let ld = self.left_distrib_eq(ge, b0e, rest_canon);
        let ge_b0 = self.mk_mul(ge, b0e);
        let ge_rest = self.mk_mul(ge, rest_canon);
        let sum = self.mk_add(ge_b0, ge_rest);
        // head: mul ge b0e ⟶ single signed monomial `prod0`.
        let (prod0, head_eq) = self.mul_mono_gen_eq(g, b0)?;
        let prod0_e = self.mono_gen_expr(prod0);
        // tail: recurse on `rest`.
        let (out_rest, rest_eq) = self.mul_gen_into_list_eq(g, rest)?;
        let out_rest_canon = self.mono_gens_to_expr(&out_rest);
        // congr both sides of `add (mul ge b0e)(mul ge rest_canon)`.
        let cong_l = self.congr_add_left(ge_b0, prod0_e, ge_rest, head_eq);
        let mid = self.mk_add(prod0_e, ge_rest);
        let cong_r = self.congr_add_right(prod0_e, ge_rest, out_rest_canon, rest_eq);
        let target = self.mk_add(prod0_e, out_rest_canon);
        let cong = self.eq_trans_r(sum, mid, target, cong_l, cong_r);
        let full = self.eq_trans_r(lhs, sum, target, ld, cong);
        // out = prod0 :: out_rest, and target IS mono_gens_to_expr(out).
        let mut out = vec![prod0];
        out.extend_from_slice(&out_rest);
        Some((out, full))
    }

    /// Distribute a full product `(mono_gens_to_expr as) * (mono_gens_to_expr bs)`
    /// of two degree-≤1 generator lists into a sum of signed monomials: prove
    /// `Eq R (mul as_canon bs_canon) (mono_gens_to_expr out)` where `out` is the
    /// Cartesian product of single-generator products. `None` if any product exceeds
    /// degree 2. Recurses on `as` with `right`-distribution (via `mul_comm` +
    /// [`Self::mul_gen_into_list_eq`]).
    fn mul_lists_eq(
        &mut self,
        a_gens: &[MonoGen],
        b_gens: &[MonoGen],
    ) -> Option<(Vec<MonoGen>, ExprId)> {
        let a_canon = self.mono_gens_to_expr(a_gens);
        let b_canon = self.mono_gens_to_expr(b_gens);
        let lhs = self.mk_mul(a_canon, b_canon);
        let Some((&a0, rest)) = a_gens.split_first() else {
            // mul zero b_canon: zero_mul not in prelude ⇒ commute then mul_zero.
            // mul zero b =[mul_comm] mul b zero =[mul_zero] zero.
            let comm = self.mul_comm_eq(a_canon, b_canon); // mul zero b = mul b zero
            let b_zero = self.mk_mul(b_canon, a_canon); // mul b zero
            let mz = self.mul_zero_eq(b_canon); // mul b zero = zero
            let zero = self.mk_zero();
            let eq = self.eq_trans_r(lhs, b_zero, zero, comm, mz);
            return Some((Vec::new(), eq));
        };
        // mul (add a0e rest_canon) b_canon — distribute on the LEFT operand.
        // No right_distrib axiom: commute to `mul b_canon (add a0e rest_canon)`,
        // left_distrib, then commute each product back.
        let a0e = self.mono_gen_expr(a0);
        let rest_canon = self.mono_gens_to_expr(rest);
        let add_a = self.mk_add(a0e, rest_canon); // = a_canon
        // mul add_a b_canon =[mul_comm] mul b_canon add_a.
        let comm0 = self.mul_comm_eq(add_a, b_canon);
        let b_adda = self.mk_mul(b_canon, add_a);
        // mul b_canon (add a0e rest_canon) =[left_distrib] add (mul b_canon a0e)(mul b_canon rest_canon).
        let ld = self.left_distrib_eq(b_canon, a0e, rest_canon);
        let b_a0 = self.mk_mul(b_canon, a0e);
        let b_rest = self.mk_mul(b_canon, rest_canon);
        let sum_b = self.mk_add(b_a0, b_rest);
        // head: mul b_canon a0e =[mul_comm] mul a0e b_canon, then distribute a0 into bs.
        let comm_h = self.mul_comm_eq(b_canon, a0e); // mul b_canon a0e = mul a0e b_canon
        let a0_b = self.mk_mul(a0e, b_canon);
        let (head_out, head_dist) = self.mul_gen_into_list_eq(a0, b_gens)?;
        let head_out_canon = self.mono_gens_to_expr(&head_out);
        let head_eq = self.eq_trans_r(b_a0, a0_b, head_out_canon, comm_h, head_dist);
        // tail: recurse on `rest`. The recursion proves about `mul rest_canon b_canon`
        // (the canonical operand order), but `left_distrib` produced `b_rest =
        // mul b_canon rest_canon`; commute first, then apply the recursive proof.
        let (tail_out, tail_inner_eq) = self.mul_lists_eq(rest, b_gens)?;
        let tail_out_canon = self.mono_gens_to_expr(&tail_out);
        let comm_t = self.mul_comm_eq(b_canon, rest_canon); // b_rest = mul rest_canon b_canon
        let rest_b = self.mk_mul(rest_canon, b_canon);
        let tail_eq = self.eq_trans_r(b_rest, rest_b, tail_out_canon, comm_t, tail_inner_eq);
        // congr both sides of `add (mul b_canon a0e)(mul b_canon rest_canon)`.
        let cong_l = self.congr_add_left(b_a0, head_out_canon, b_rest, head_eq);
        let mid = self.mk_add(head_out_canon, b_rest);
        let cong_r = self.congr_add_right(head_out_canon, b_rest, tail_out_canon, tail_eq);
        // append head_out ++ tail_out to a single right-nested canonical sum.
        let appended = self.mono_append_eq(&head_out, &tail_out);
        let mut out: Vec<MonoGen> = head_out.clone();
        out.extend_from_slice(&tail_out);
        let out_canon = self.mono_gens_to_expr(&out);
        let pre_target = self.mk_add(head_out_canon, tail_out_canon);
        let cong = self.eq_trans_r(sum_b, mid, pre_target, cong_l, cong_r);
        // Chain: lhs =[comm0] b_adda =[ld] sum_b =[cong] pre_target =[appended] out_canon.
        let t01 = self.eq_trans_r(lhs, b_adda, sum_b, comm0, ld);
        let t02 = self.eq_trans_r(lhs, sum_b, pre_target, t01, cong);
        let full = self.eq_trans_r(lhs, pre_target, out_canon, t02, appended);
        Some((out, full))
    }

    /// Reduce a product of two single signed generators (each degree ≤ 1) to a
    /// single signed monomial: prove
    /// `Eq R (mul (mono_gen_expr a)(mono_gen_expr b)) (mono_gen_expr out)`.
    /// Handles the four sign combinations via the derived neg-bridge lemmas
    /// (`mul_neg_right`/`mul_neg_left`/`neg_mul_neg`) and `mul_one`/`mul_comm` for
    /// the constant factor. Returns `None` if either factor is quadratic (the product
    /// would exceed degree 2 — out of scope).
    fn mul_mono_gen_eq(&mut self, a: MonoGen, b: MonoGen) -> Option<(MonoGen, ExprId)> {
        // The unsigned monomial product (both must be degree ≤ 1).
        let (out_mono, base_eq) = self.mul_base_mono_eq(a.mono, b.mono)?;
        let ae = self.mono_expr(a.mono);
        let be = self.mono_expr(b.mono);
        let out_e = self.mono_expr(out_mono);
        // Resulting sign is the XOR of the input signs.
        let out_neg = a.neg ^ b.neg;
        let out_gen = MonoGen {
            mono: out_mono,
            neg: out_neg,
        };
        // The LHS as built by `mono_gen_expr`: `mul (sign ae)(sign be)`.
        let lhs_a = if a.neg { self.mk_neg(ae) } else { ae };
        let lhs_b = if b.neg { self.mk_neg(be) } else { be };
        let lhs = self.mk_mul(lhs_a, lhs_b);
        // Strip the signs down to `mul ae be`, tracking the accumulated outer neg.
        // Case on the sign pattern; `base_eq : Eq R (mul ae be) out_e`.
        let ab = self.mk_mul(ae, be);
        let proof = match (a.neg, b.neg) {
            (false, false) => {
                // lhs = mul ae be IS `ab` (no signs); base_eq : Eq R ab out_e.
                base_eq
            }
            (true, false) => {
                // lhs = mul (neg ae) be =[mul_neg_left] neg (mul ae be) =[congr_neg base] neg out_e.
                let mnl = self.mul_neg_left_eq(ae, be); // mul (neg ae) be = neg (ab)
                let neg_ab = self.mk_neg(ab);
                let neg_out = self.mk_neg(out_e);
                let cong = self.congr_neg(ab, out_e, base_eq); // neg ab = neg out_e
                self.eq_trans_r(lhs, neg_ab, neg_out, mnl, cong)
            }
            (false, true) => {
                // lhs = mul ae (neg be) =[mul_neg_right] neg (mul ae be) =[congr_neg base] neg out_e.
                let mnr = self.mul_neg_right_eq(ae, be); // mul ae (neg be) = neg ab
                let neg_ab = self.mk_neg(ab);
                let neg_out = self.mk_neg(out_e);
                let cong = self.congr_neg(ab, out_e, base_eq);
                self.eq_trans_r(lhs, neg_ab, neg_out, mnr, cong)
            }
            (true, true) => {
                // lhs = mul (neg ae)(neg be) =[neg_mul_neg] mul ae be =[base] out_e.
                let nmn = self.neg_mul_neg_eq(ae, be); // mul (neg ae)(neg be) = ab
                self.eq_trans_r(lhs, ab, out_e, nmn, base_eq)
            }
        };
        Some((out_gen, proof))
    }

    /// Reduce an UNSIGNED product `mul (mono_expr a)(mono_expr b)` of two degree-≤1
    /// base monomials to a single base monomial, proving
    /// `Eq R (mul (mono_expr a)(mono_expr b)) (mono_expr out)`. `None` if either is
    /// [`Mono::Quad`] (product degree ≥ 3 — out of scope).
    fn mul_base_mono_eq(&mut self, a: Mono, b: Mono) -> Option<(Mono, ExprId)> {
        match (a, b) {
            (Mono::Quad(..), _) | (_, Mono::Quad(..)) => None,
            (Mono::Const, Mono::Const) => {
                // mul one one =[mul_one one] one.
                let one = self.mk_one();
                let mo = self.mul_one_eq(one); // mul one one = one
                Some((Mono::Const, mo))
            }
            (Mono::Const, other) | (other, Mono::Const) => {
                // mul one v =[mul_comm] mul v one =[mul_one] v  (or mul v one directly).
                let one = self.mk_one();
                let ve = self.mono_expr(other);
                // Determine actual operand order in `mul (mono_expr a)(mono_expr b)`.
                let (le, re, is_one_left) = if matches!(a, Mono::Const) {
                    (one, ve, true)
                } else {
                    (ve, one, false)
                };
                let lhs = self.mk_mul(le, re);
                let eq = if is_one_left {
                    // mul one v =[mul_comm] mul v one =[mul_one] v.
                    let comm = self.mul_comm_eq(one, ve);
                    let v_one = self.mk_mul(ve, one);
                    let mo = self.mul_one_eq(ve);
                    self.eq_trans_r(lhs, v_one, ve, comm, mo)
                } else {
                    // mul v one =[mul_one] v.
                    self.mul_one_eq(ve)
                };
                Some((other, eq))
            }
            (Mono::Lin(i), Mono::Lin(j)) => {
                // mul xi xj is already a base monomial `Quad(min,max)`.
                let xi = self.mono_expr(Mono::Lin(i));
                let xj = self.mono_expr(Mono::Lin(j));
                let lhs = self.mk_mul(xi, xj);
                let out = Mono::quad(i, j);
                if i <= j {
                    // out = Quad(i,j) ⇒ mono_expr(out) = mul xi xj = lhs ⇒ refl.
                    Some((out, self.eq_refl_r(lhs)))
                } else {
                    // out = Quad(j,i) ⇒ mono_expr(out) = mul xj xi; lhs = mul xi xj.
                    // mul xi xj =[mul_comm] mul xj xi.
                    let comm = self.mul_comm_eq(xi, xj);
                    Some((out, comm))
                }
            }
        }
    }

    /// `mul_one a : Eq R (mul a one) a`.
    fn mul_one_eq(&mut self, a: ExprId) -> ExprId {
        let ax = self.kernel.const_(self.arith.mul_one, vec![]);
        self.kernel.app(ax, a)
    }

    /// Emit just the faithful kernel `R`-encoding of an [`RExpr`] (no proof). The
    /// kernel hash-conses structurally, so this yields the SAME [`ExprId`] the
    /// normalizer's `kernel_expr` carries for the same `RExpr`.
    fn emit_rexpr(&mut self, expr: &RExpr) -> ExprId {
        match expr {
            RExpr::Var(i) => {
                let name = self.var_const(*i);
                self.kernel.const_(name, vec![])
            }
            RExpr::One => self.mk_one(),
            RExpr::Neg(a) => {
                let ae = self.emit_rexpr(a);
                self.mk_neg(ae)
            }
            RExpr::Add(a, b) => {
                let ae = self.emit_rexpr(a);
                let be = self.emit_rexpr(b);
                self.mk_add(ae, be)
            }
            RExpr::Mul(a, b) => {
                let ae = self.emit_rexpr(a);
                let be = self.emit_rexpr(b);
                self.mk_mul(ae, be)
            }
        }
    }

    /// **Degree-2 ring normalizer** (ADR-0040 generalization). Recursively rewrite an
    /// [`RExpr`] of total degree ≤ 2 into a canonical signed-monomial sum, returning
    /// `(gens, kernel_expr, proof)` with `proof : Eq R kernel_expr (mono_gens_to_expr
    /// gens)` and `gens` the SORTED-AND-CANCELLED canonical generators. `kernel_expr`
    /// is the faithful encoding of the input. Returns `None` (decline) if any
    /// subproduct would exceed degree 2.
    ///
    /// Two `RExpr`s with the SAME canonical `gens` are provably equal over `R`:
    /// `Eq R e1 e2 = trans (proof1) (symm proof2)`. The asserted-polynomial identity
    /// `Eq R pK sqK` is assembled exactly this way (after confirming the two `gens`
    /// agree — which the SOS certificate guarantees, but the reconstructor checks).
    fn normalize_deg2(&mut self, expr: &RExpr) -> Option<(Vec<MonoGen>, ExprId, ExprId)> {
        // First produce the raw (unsorted) gens + a proof `Eq R expr raw_canon`,
        // then run the additive normalizer to sort & cancel.
        let (raw_gens, kernel_expr, raw_proof) = self.normalize_deg2_raw(expr)?;
        let (canon_gens, sort_proof) = self.mono_normalize_gens(&raw_gens);
        let raw_canon = self.mono_gens_to_expr(&raw_gens);
        let canon = self.mono_gens_to_expr(&canon_gens);
        // proof : Eq R expr canon = trans raw_proof sort_proof.
        let proof = self.eq_trans_r(kernel_expr, raw_canon, canon, raw_proof, sort_proof);
        Some((canon_gens, kernel_expr, proof))
    }

    /// The recursive core of [`Self::normalize_deg2`]: returns `(raw_gens,
    /// kernel_expr, proof)` with `proof : Eq R kernel_expr (mono_gens_to_expr
    /// raw_gens)`, where `raw_gens` is NOT yet sorted/cancelled. `None` on a
    /// degree-≥3 subproduct.
    fn normalize_deg2_raw(&mut self, expr: &RExpr) -> Option<(Vec<MonoGen>, ExprId, ExprId)> {
        match expr {
            RExpr::Var(i) => {
                let name = self.var_const(*i);
                let xe = self.kernel.const_(name, vec![]);
                // xi = add xi zero  (symm add_zero).
                let zero = self.mk_zero();
                let xz = self.mk_add(xe, zero);
                let az = self.add_zero_eq(xe); // add xi zero = xi
                let proof = self.eq_symm_r(xz, xe, az); // xi = add xi zero
                Some((vec![MonoGen::pos(Mono::Lin(*i))], xe, proof))
            }
            RExpr::One => {
                let one_e = self.mk_one();
                let zero = self.mk_zero();
                let oz = self.mk_add(one_e, zero);
                let az = self.add_zero_eq(one_e);
                let proof = self.eq_symm_r(oz, one_e, az);
                Some((vec![MonoGen::pos(Mono::Const)], one_e, proof))
            }
            RExpr::Neg(a) => {
                let (a_gens, a_e, a_proof) = self.normalize_deg2_raw(a)?;
                let neg_e = self.mk_neg(a_e);
                let a_canon = self.mono_gens_to_expr(&a_gens);
                // neg a_e =[congr_neg a_proof] neg a_canon =[neg_gens] canon(neg gens).
                let cong = self.congr_neg(a_e, a_canon, a_proof); // neg a_e = neg a_canon
                let neg_a_canon = self.mk_neg(a_canon);
                let neg_gens: Vec<MonoGen> = a_gens.iter().map(|g| g.negate()).collect();
                let neg_gens_eq = self.mono_neg_gens_eq(&a_gens); // neg a_canon = canon(neg gens)
                let out_canon = self.mono_gens_to_expr(&neg_gens);
                let proof = self.eq_trans_r(neg_e, neg_a_canon, out_canon, cong, neg_gens_eq);
                Some((neg_gens, neg_e, proof))
            }
            RExpr::Add(a, b) => {
                let (a_gens, a_e, a_proof) = self.normalize_deg2_raw(a)?;
                let (b_gens, b_e, b_proof) = self.normalize_deg2_raw(b)?;
                let add_e = self.mk_add(a_e, b_e);
                let a_canon = self.mono_gens_to_expr(&a_gens);
                let b_canon = self.mono_gens_to_expr(&b_gens);
                // add a_e b_e =[congr both] add a_canon b_canon =[append] canon(a++b).
                let cong_l = self.congr_add_left(a_e, a_canon, b_e, a_proof);
                let mid = self.mk_add(a_canon, b_e);
                let cong_r = self.congr_add_right(a_canon, b_e, b_canon, b_proof);
                let ab_canon = self.mk_add(a_canon, b_canon);
                let cong = self.eq_trans_r(add_e, mid, ab_canon, cong_l, cong_r);
                let appended = self.mono_append_eq(&a_gens, &b_gens);
                let mut out: Vec<MonoGen> = a_gens.clone();
                out.extend_from_slice(&b_gens);
                let out_canon = self.mono_gens_to_expr(&out);
                let proof = self.eq_trans_r(add_e, ab_canon, out_canon, cong, appended);
                Some((out, add_e, proof))
            }
            RExpr::Mul(a, b) => {
                let (a_gens, a_e, a_proof) = self.normalize_deg2_raw(a)?;
                let (b_gens, b_e, b_proof) = self.normalize_deg2_raw(b)?;
                let mul_e = self.mk_mul(a_e, b_e);
                let a_canon = self.mono_gens_to_expr(&a_gens);
                let b_canon = self.mono_gens_to_expr(&b_gens);
                // mul a_e b_e =[congr both] mul a_canon b_canon =[distribute] canon(out).
                let cong_l = self.congr_mul_left(a_e, a_canon, b_e, a_proof);
                let mid = self.mk_mul(a_canon, b_e);
                let cong_r = self.congr_mul_right(a_canon, b_e, b_canon, b_proof);
                let ab_canon = self.mk_mul(a_canon, b_canon);
                let cong = self.eq_trans_r(mul_e, mid, ab_canon, cong_l, cong_r);
                let (out, dist) = self.mul_lists_eq(&a_gens, &b_gens)?;
                let out_canon = self.mono_gens_to_expr(&out);
                let proof = self.eq_trans_r(mul_e, ab_canon, out_canon, cong, dist);
                Some((out, mul_e, proof))
            }
        }
    }

    /// Cast the right operand of a `le`: given `h_le : le l r` and
    /// `h_eq : Eq R r r'`, build `le l r'`.
    fn le_cast_right(
        &mut self,
        l: ExprId,
        r: ExprId,
        rp: ExprId,
        h_le: ExprId,
        h_eq: ExprId,
    ) -> ExprId {
        // motive := fun (x : R) (_ : Eq R r x) => le l x.
        let motive = {
            let x1 = self.kernel.bvar(1);
            let le_l_x = self.mk_le(l, x1);
            let x0 = self.kernel.bvar(0);
            let eq_r_x = self.mk_eq_r(r, x0);
            let anon = self.kernel.anon();
            let inner = self.kernel.lam(anon, eq_r_x, le_l_x, BinderInfo::Default);
            let r_ty = self.kernel.const_(self.arith.r, vec![]);
            self.kernel.lam(anon, r_ty, inner, BinderInfo::Default)
        };
        self.eq_rec_transport_r(r, motive, h_le, rp, h_eq)
    }

    /// Cast the left operand of a `le`: given `h_le : le l r` and
    /// `h_eq : Eq R l l'`, build `le l' r`.
    fn le_cast_left(
        &mut self,
        l: ExprId,
        lp: ExprId,
        r: ExprId,
        h_le: ExprId,
        h_eq: ExprId,
    ) -> ExprId {
        // motive := fun (x : R) (_ : Eq R l x) => le x r.
        let motive = {
            let x1 = self.kernel.bvar(1);
            let le_x_r = self.mk_le(x1, r);
            let x0 = self.kernel.bvar(0);
            let eq_l_x = self.mk_eq_r(l, x0);
            let anon = self.kernel.anon();
            let inner = self.kernel.lam(anon, eq_l_x, le_x_r, BinderInfo::Default);
            let r_ty = self.kernel.const_(self.arith.r, vec![]);
            self.kernel.lam(anon, r_ty, inner, BinderInfo::Default)
        };
        self.eq_rec_transport_r(l, motive, h_le, lp, h_eq)
    }

    /// `add_le_add a b c d h1 h2 : le (add a c) (add b d)`.
    fn add_le_add_app(
        &mut self,
        a: ExprId,
        b: ExprId,
        c: ExprId,
        d: ExprId,
        h1: ExprId,
        h2: ExprId,
    ) -> ExprId {
        let ax = self.kernel.const_(self.arith.add_le_add, vec![]);
        let e = self.kernel.app(ax, a);
        let e = self.kernel.app(e, b);
        let e = self.kernel.app(e, c);
        let e = self.kernel.app(e, d);
        let e = self.kernel.app(e, h1);
        self.kernel.app(e, h2)
    }

    /// `add_lt_add_of_le_of_lt a b c d h1 h2 : lt (add a c)(add b d)` from
    /// `h1 : le a b`, `h2 : lt c d`. Summing a non-strict with a strict ⇒ strict.
    fn add_lt_add_of_le_of_lt_app(
        &mut self,
        a: ExprId,
        b: ExprId,
        c: ExprId,
        d: ExprId,
        h1: ExprId,
        h2: ExprId,
    ) -> ExprId {
        let ax = self
            .kernel
            .const_(self.arith.add_lt_add_of_le_of_lt, vec![]);
        let e = self.kernel.app(ax, a);
        let e = self.kernel.app(e, b);
        let e = self.kernel.app(e, c);
        let e = self.kernel.app(e, d);
        let e = self.kernel.app(e, h1);
        self.kernel.app(e, h2)
    }

    /// `le_of_lt a b h : le a b` from `h : lt a b`.
    fn le_of_lt_app(&mut self, a: ExprId, b: ExprId, h: ExprId) -> ExprId {
        let ax = self.kernel.const_(self.arith.le_of_lt, vec![]);
        let e = self.kernel.app(ax, a);
        let e = self.kernel.app(e, b);
        self.kernel.app(e, h)
    }

    /// Derived `add_lt_add a b c d h1 h2 : lt (add a c)(add b d)` from
    /// `h1 : lt a b`, `h2 : lt c d`. No new axiom: weaken `h1` to `le a b`
    /// (`le_of_lt`) and apply [`Self::add_lt_add_of_le_of_lt_app`].
    fn add_lt_add_app(
        &mut self,
        a: ExprId,
        b: ExprId,
        c: ExprId,
        d: ExprId,
        h1: ExprId,
        h2: ExprId,
    ) -> ExprId {
        let h1_le = self.le_of_lt_app(a, b, h1);
        self.add_lt_add_of_le_of_lt_app(a, b, c, d, h1_le, h2)
    }

    /// Cast the left operand of a `lt`: `h_lt : lt l r`, `h_eq : Eq R l l'` ⇒ `lt l' r`.
    fn lt_cast_left(
        &mut self,
        l: ExprId,
        lp: ExprId,
        r: ExprId,
        h_lt: ExprId,
        h_eq: ExprId,
    ) -> ExprId {
        let motive = {
            let x1 = self.kernel.bvar(1);
            let lt_x_r = self.mk_lt(x1, r);
            let x0 = self.kernel.bvar(0);
            let eq_l_x = self.mk_eq_r(l, x0);
            let anon = self.kernel.anon();
            let inner = self.kernel.lam(anon, eq_l_x, lt_x_r, BinderInfo::Default);
            let r_ty = self.kernel.const_(self.arith.r, vec![]);
            self.kernel.lam(anon, r_ty, inner, BinderInfo::Default)
        };
        self.eq_rec_transport_r(l, motive, h_lt, lp, h_eq)
    }

    /// `lt_of_lt_of_le a b c h1 h2 : lt a c` from `h1 : lt a b`, `h2 : le b c`.
    fn lt_of_lt_of_le_app(
        &mut self,
        a: ExprId,
        b: ExprId,
        c: ExprId,
        h1: ExprId,
        h2: ExprId,
    ) -> ExprId {
        let ax = self.kernel.const_(self.arith.lt_of_lt_of_le, vec![]);
        let e = self.kernel.app(ax, a);
        let e = self.kernel.app(e, b);
        let e = self.kernel.app(e, c);
        let e = self.kernel.app(e, h1);
        self.kernel.app(e, h2)
    }

    /// Build a proof `lt zero K` where `K = gens_to_expr` of `n ≥ 1` `One` generators,
    /// i.e. `K = one + (one + … + (one + zero))`. Built by partial-sum induction:
    /// `lt zero one` (`zero_lt_one`), then for each extra `one`, extend `lt zero S` to
    /// `lt zero (one + S)` via `le S (one + S)` and `lt_of_lt_of_le`.
    fn lt_zero_ones(&mut self, n: i128) -> ExprId {
        debug_assert!(n >= 1);
        // S_1 = one + zero ; prove lt zero S_1 from zero_lt_one : lt zero one and
        // one =[symm add_zero one] one + zero.
        let one = self.mk_one();
        let zero = self.mk_zero();
        let one_zero = self.mk_add(one, zero); // gens_to_expr([One]) = one + zero
        let zlo = self.kernel.const_(self.arith.zero_lt_one, vec![]); // lt zero one
        // cast the rhs `one → one+zero` using symm (add_zero one) : Eq one (one+zero).
        let addz = self.add_zero_eq(one); // add one zero = one
        let eq_one_onezero = self.eq_symm_r(one_zero, one, addz); // one = one+zero
        // le_cast_right on lt? We only have le_cast for `le`. Build a lt-cast.
        let mut acc = self.lt_cast_right(zero, one, one_zero, zlo, eq_one_onezero); // lt zero (one+zero)
        let mut s_gens = vec![Gen::One];
        for _ in 1..n {
            // Extend acc : lt zero S to lt zero (one + S).
            let s = self.gens_to_expr(&s_gens);
            let mut new_gens = vec![Gen::One];
            new_gens.extend_from_slice(&s_gens);
            let new_s = self.gens_to_expr(&new_gens); // one + S
            // Need le S (one + S). Build via add_le_add: le zero one (le_of_lt zlo)
            //   and le S S (le_refl S) ⇒ le (zero + S)(one + S); then cast lhs zero+S → S.
            let le_zero_one = {
                let lo = self.kernel.const_(self.arith.le_of_lt, vec![]);
                let zlo2 = self.kernel.const_(self.arith.zero_lt_one, vec![]);
                let e = self.kernel.app(lo, zero);
                let e = self.kernel.app(e, one);
                self.kernel.app(e, zlo2)
            }; // le zero one
            let le_s_s = {
                let lr = self.kernel.const_(self.arith.le_refl, vec![]);
                self.kernel.app(lr, s)
            }; // le S S
            // add_le_add zero one S S : le (add zero S)(add one S)
            let combined = self.add_le_add_app(zero, one, s, s, le_zero_one, le_s_s);
            // cast lhs (add zero S) → S via add_comm + add_zero.
            let zs = self.mk_add(zero, s);
            let comm = self.add_comm_eq(zero, s); // add zero S = add S zero
            let addz_s = self.add_zero_eq(s); // add S zero = S
            let sz = self.mk_add(s, zero);
            let eq_zs_s = self.eq_trans_r(zs, sz, s, comm, addz_s); // add zero S = S
            let le_s_news = self.le_cast_left(zs, s, new_s, combined, eq_zs_s); // le S (one+S)
            // lt_of_lt_of_le zero S (one+S) acc le_s_news : lt zero (one+S).
            acc = self.lt_of_lt_of_le_app(zero, s, new_s, acc, le_s_news);
            s_gens = new_gens;
        }
        acc
    }

    /// Cast the right operand of a `lt`: `h_lt : lt l r`, `h_eq : Eq R r r'` ⇒ `lt l r'`.
    fn lt_cast_right(
        &mut self,
        l: ExprId,
        r: ExprId,
        rp: ExprId,
        h_lt: ExprId,
        h_eq: ExprId,
    ) -> ExprId {
        let motive = {
            let x1 = self.kernel.bvar(1);
            let lt_l_x = self.mk_lt(l, x1);
            let x0 = self.kernel.bvar(0);
            let eq_r_x = self.mk_eq_r(r, x0);
            let anon = self.kernel.anon();
            let inner = self.kernel.lam(anon, eq_r_x, lt_l_x, BinderInfo::Default);
            let r_ty = self.kernel.const_(self.arith.r, vec![]);
            self.kernel.lam(anon, r_ty, inner, BinderInfo::Default)
        };
        self.eq_rec_transport_r(r, motive, h_lt, rp, h_eq)
    }

    /// Scale-and-sum a list of integer-coefficient atoms `(Eᵢ, μᵢ)` (`μᵢ ≥ 1`) into a
    /// single `rel Lsum zero` proof, where `rel` is `le` when `strict == false` and
    /// `lt` when `strict == true`. Mirrors the non-strict summation inside
    /// [`try_general_farkas`], but routes through the strict combinators when `strict`:
    /// `add_lt_add` for the scale/fold steps and `lt_cast_*` for the renormalizations.
    /// The per-atom hypothesis is `hᵢ : rel Eᵢ zero` (same relation).
    ///
    /// Returns `(proof, gens)` where `gens` is the canonical generator list of `Lsum`
    /// (so `gens_to_expr(gens)` is the proof's LHS), or `None` if any atom has a
    /// non-integer coefficient/constant. The caller normalizes `gens` to the combined
    /// constant. `atoms` must be non-empty.
    fn sum_scaled_atoms(
        &mut self,
        atoms: &[(LinR, i128)],
        strict: bool,
    ) -> Result<Option<(ExprId, Vec<Gen>)>, ReconstructError> {
        let zero = self.mk_zero();
        let mut acc: Option<(ExprId, Vec<Gen>)> = None; // (rel-proof, gens)
        for (lin, mu) in atoms {
            let Some(base_gens) = LraReconstructCtx::lin_to_gens(lin) else {
                return Ok(None);
            };
            let base_expr = self.gens_to_expr(&base_gens);
            // hypothesis hᵢ : rel base_expr zero.
            let prop = if strict {
                self.mk_lt(base_expr, zero)
            } else {
                self.mk_le(base_expr, zero)
            };
            let h = self.hyp_axiom(prop)?;
            // Scale by μᵢ: fold hᵢ with itself μᵢ times, keeping RHS = zero and the LHS
            // in canonical generator form.
            let mut s_proof = h;
            let mut s_gens = base_gens.clone();
            let mut s_expr = base_expr;
            for _ in 1..*mu {
                let combined = if strict {
                    self.add_lt_add_app(s_expr, zero, base_expr, zero, s_proof, h)
                } else {
                    self.add_le_add_app(s_expr, zero, base_expr, zero, s_proof, h)
                };
                let lhs = self.mk_add(s_expr, base_expr);
                // RHS (add zero zero) → zero.
                let azz = self.add_zero_eq(zero);
                let add_zz = self.mk_add(zero, zero);
                let combined = if strict {
                    self.lt_cast_right(lhs, add_zz, zero, combined, azz)
                } else {
                    self.le_cast_right(lhs, add_zz, zero, combined, azz)
                };
                // LHS (add s_expr base_expr) → canonical (s_gens ++ base_gens).
                let mut next_gens = s_gens.clone();
                next_gens.extend_from_slice(&base_gens);
                let append_proof = self.append_eq(&s_gens, &base_gens);
                let next_canon = self.gens_to_expr(&next_gens);
                s_proof = if strict {
                    self.lt_cast_left(lhs, next_canon, zero, combined, append_proof)
                } else {
                    self.le_cast_left(lhs, next_canon, zero, combined, append_proof)
                };
                s_gens = next_gens;
                s_expr = next_canon;
            }
            // Fold this scaled constraint into the accumulator.
            acc = Some(match acc {
                None => (s_proof, s_gens),
                Some((acc_proof, acc_gens)) => {
                    let acc_expr = self.gens_to_expr(&acc_gens);
                    let combined = if strict {
                        self.add_lt_add_app(acc_expr, zero, s_expr, zero, acc_proof, s_proof)
                    } else {
                        self.add_le_add_app(acc_expr, zero, s_expr, zero, acc_proof, s_proof)
                    };
                    let azz = self.add_zero_eq(zero);
                    let add_zz = self.mk_add(zero, zero);
                    let lhs = self.mk_add(acc_expr, s_expr);
                    let combined = if strict {
                        self.lt_cast_right(lhs, add_zz, zero, combined, azz)
                    } else {
                        self.le_cast_right(lhs, add_zz, zero, combined, azz)
                    };
                    let mut next_gens = acc_gens.clone();
                    next_gens.extend_from_slice(&s_gens);
                    let append_proof = self.append_eq(&acc_gens, &s_gens);
                    let next_canon = self.gens_to_expr(&next_gens);
                    let new_proof = if strict {
                        self.lt_cast_left(lhs, next_canon, zero, combined, append_proof)
                    } else {
                        self.le_cast_left(lhs, next_canon, zero, combined, append_proof)
                    };
                    (new_proof, next_gens)
                }
            });
        }
        Ok(acc)
    }

    /// Build the generator list of a [`LinR`] whose coefficients and constant are all
    /// integers: each variable `(i, c)` contributes `|c|` copies of `Var(i)`/`NegVar(i)`,
    /// then the constant contributes `|k|` copies of `One`/`NegOne`. Returns `None` if
    /// any coefficient or the constant is not an integer (outside this engine's scope).
    fn lin_to_gens(lin: &LinR) -> Option<Vec<Gen>> {
        let mut gens = Vec::new();
        for &(index, coeff) in &lin.coeffs {
            if coeff.denominator() != 1 {
                return None;
            }
            let n = coeff.numerator();
            let (g, count) = if n >= 0 {
                (Gen::Var(index), n)
            } else {
                (Gen::NegVar(index), -n)
            };
            for _ in 0..count {
                gens.push(g);
            }
        }
        if lin.constant.denominator() != 1 {
            return None;
        }
        let k = lin.constant.numerator();
        let (g, count) = if k >= 0 {
            (Gen::One, k)
        } else {
            (Gen::NegOne, -k)
        };
        for _ in 0..count {
            gens.push(g);
        }
        Some(gens)
    }
}

/// Reconstruct a small real `QF_LRA` `unsat` instance into a Lean proof term of
/// type `False` that the trusted [`Kernel`] type-checks, by way of its Farkas
/// (`la_generic`) certificate.
///
/// The instance is `assertions` over `arena`, a conjunction of linear-real order
/// constraints. The certificate is obtained from [`crate::lra_farkas_certificate`]
/// (the real, self-checked Fourier–Motzkin Farkas refutation), so this only
/// returns a term when the instance is genuinely `unsat`. The returned
/// [`ExprId`]'s inferred type is [`Kernel::def_eq`] to the prelude's `False`.
///
/// **Scope (slice 1):** only the *transitivity-reducible* two-constraint shape is
/// reconstructed — an instance equivalent to `e ≤ 0 ∧ 1 ≤ e` over a shared `R`
/// expression `e` with small `{-1,0,+1}` coefficients. This is the baby-Farkas
/// order chain (`le_trans` → `lt_of_le_of_lt` with `zero_lt_one` → `lt_irrefl`),
/// needing no ring sum. Any other cert shape (general multipliers, a ring
/// cancellation, more than two participating constraints, non-`{-1,0,+1}`
/// coefficients) is rejected with a clear error — a later slice.
///
/// # Errors
///
/// Returns [`ReconstructError::MalformedStep`] if `assertions` is not `unsat`
/// through the Farkas path or its shape is outside slice 1,
/// [`ReconstructError::UnsupportedTerm`] for a constraint outside the small linear
/// subset this slice models, and [`ReconstructError::KernelRejected`] when the
/// kernel's `infer` fails or the inferred proposition is not `def_eq` to `False`.
/// It never panics on out-of-scope input.
#[allow(dead_code)]
pub fn reconstruct_lra_proof(
    ctx: &mut LraReconstructCtx,
    arena: &TermArena,
    assertions: &[TermId],
) -> Result<ExprId, ReconstructError> {
    // Obtain the REAL, self-checked Farkas certificate. `None` ⇒ the instance is
    // not unsat through the Farkas path (sat, or a trivially-false assertion).
    let certificate = match crate::lra_farkas_certificate(arena, assertions) {
        Ok(Some(cert)) => cert,
        Ok(None) => {
            return Err(ReconstructError::MalformedStep {
                rule: "la_generic".to_owned(),
                detail: "instance is not unsat through the Farkas path (sat or trivial)".to_owned(),
            });
        }
        Err(e) => {
            return Err(ReconstructError::MalformedStep {
                rule: "la_generic".to_owned(),
                detail: format!("LRA decision failed: {e}"),
            });
        }
    };
    // Strict-`<` cycle `e0<e1<…<e_{n-1}<e0` (n≥2): fold `lt_trans` to `lt e0 e0`,
    // then `lt_irrefl`. Tried first; falls through to the `≤` baby-Farkas shape.
    if let Some(proof) = try_strict_cycle(ctx, arena, assertions, &certificate)? {
        return Ok(proof);
    }
    // Mixed strict/non-strict Farkas: at least one used atom is strict (`<`) and the
    // combination is not a pure strict cycle. Sum the strict atoms into `lt Lst 0`, the
    // non-strict into `le Lne 0`, combine to `lt (Lst+Lne) 0`, normalize to the constant
    // `K ≥ 0`, and close (`lt_irrefl` directly for `K = 0`, or via `lt_trans` with
    // `0 < K` otherwise). Tried before the pure non-strict engine, which rejects strict
    // atoms.
    if let Some(proof) = try_mixed_farkas(ctx, &certificate)? {
        return Ok(proof);
    }
    // General Farkas over non-strict integer-coefficient constraints with arbitrary
    // nonnegative (rational, denominator-cleared) multipliers: scale every used
    // `Eᵢ ≤ 0` atom by an integer `μᵢ`, sum with `add_le_add`, normalize the sum's
    // variable terms to cancel (the ring engine), and close `K ≤ 0` against `0 < K`.
    if let Some(proof) = try_general_farkas(ctx, &certificate)? {
        return Ok(proof);
    }
    reconstruct_transitivity_refutation(ctx, arena, assertions, &certificate)
}

/// Reconstruct the **trivial single-square sum-of-squares** refutation
/// (ADR-0040, SOS slice 1): the one-variable real query `x*x < 0`, which is UNSAT
/// because a real square is never negative.
///
/// This is the simplest SOS reconstruction and needs **no ring normalizer** — the
/// SOS identity `x² = 1·x²` is trivial — so the proof is just unconditional
/// square-nonnegativity composed with one order step:
///
/// 1. `sq  : le zero (mul x x)` := `sq_nonneg x` (the prelude's unconditional
///    square-nonnegativity axiom applied to the variable term `x`).
/// 2. `hlt : lt (mul x x) zero` — the asserted atom `x*x < 0`, introduced as a
///    hypothesis axiom (mirroring how the LRA baby-Farkas path discharges its
///    asserted constraints via `LraReconstructCtx::hyp_axiom`).
/// 3. `chain : lt zero zero` := `lt_of_le_of_lt zero (mul x x) zero sq hlt`.
/// 4. `bad : False` := `lt_irrefl zero chain` (since
///    `lt_irrefl zero : Not (lt zero zero) = lt zero zero → False`).
///
/// The returned [`ExprId`] infers to `False` and is gated (`infer` + `def_eq
/// False`) here; a wrong reconstruction is [`ReconstructError::KernelRejected`],
/// never an accepted unsound proof.
///
/// # Errors
///
/// Returns [`ReconstructError::UnsupportedTerm`] for **anything but** the trivial
/// single-square shape `mul x x < 0` over one real variable (general SOS such as
/// `(x − y)² < 0` is a later slice and is declined here), or
/// [`ReconstructError::KernelRejected`] if the assembled term fails to kernel-check
/// to `False`.
pub fn reconstruct_sos_proof(
    ctx: &mut LraReconstructCtx,
    arena: &TermArena,
    assertions: &[TermId],
) -> Result<ExprId, ReconstructError> {
    // Accept the single-square shape `ℓ*ℓ < 0` where `ℓ` is a linear form in
    // `lin_to_r`'s slice (a bare variable `x`, or `(x−y)`, etc.). The asserted lhs
    // is literally `ℓ·ℓ`, so no ring normalizer is needed.
    //
    // Otherwise try the degree-2 two-variable AM-GM sum form `x²+y²−2xy < 0` —
    // the first shape needing the ring normalizer (the lhs is a *sum* of
    // monomials, proven equal to `(x−y)·(x−y)` in the kernel before
    // square-nonnegativity applies).
    //
    // Anything else (a coefficient outside ±1, other monomial sets, ≥ 3 variables)
    // is declined here so we never claim success without a kernel-checked term.
    let Some(factor) = is_single_square_lt_zero(arena, assertions) else {
        // Fast path: the hard-coded two-variable AM-GM shape (kept working).
        if let Some((sx, sy)) = is_am_gm_two_var(arena, assertions) {
            return reconstruct_am_gm_two_var(ctx, sx, sy);
        }
        // General path: any query whose SOS certificate is a single perfect square
        // of a ±1-coefficient linear form (e.g. `(x+y)² < 0`, `(x−z)² < 0`). Driven
        // by the SOS certificate (not a per-shape IR matcher) and the degree-2 ring
        // normalizer. Declines (falls through to the error) for multi-square / `d≠1`
        // / scaled-coefficient certificates.
        if let Some(proof) = reconstruct_sos_single_unit_square(ctx, arena, assertions)? {
            return Ok(proof);
        }
        // General path: any query whose SOS certificate is a SUM of several perfect
        // squares of ±1-coefficient linear forms (e.g. `x²+y² < 0`, `x²+y²+z² < 0`),
        // every `d = 1`, zero affine. Folds square-nonnegativity over the squares.
        if let Some(proof) = reconstruct_sos_multi_unit_square(ctx, arena, assertions)? {
            return Ok(proof);
        }
        // General path: any query whose SOS certificate is a RATIONAL-weight sum of
        // squares `p = Σ dₖ·ℓₖ²` (rational weights, rational/integer linear forms,
        // zero affine) — unlocks 3-variable AM-GM. Clears denominators so the proof
        // reduces to the integer fold (`M·p = Σ(M·wₖ)(ℓₖ⁺)²`); no scaling lemma.
        if let Some(proof) = reconstruct_sos_rational_weight(ctx, arena, assertions)? {
            return Ok(proof);
        }
        // Strict-inequality DUAL: any query whose SOS certificate refutes `p > 0`
        // (`strict_lt == false`) — the certificate's squares decompose `−p`. Mirrors
        // the `p < 0` rational-weight fold, closing via the exact `sosK + mpK = 0`
        // cancellation (sosK = `−(M·p)`, mpK = `M·p`).
        if let Some(proof) = reconstruct_sos_rational_weight_gt(ctx, arena, assertions)? {
            return Ok(proof);
        }
        return Err(ReconstructError::UnsupportedTerm {
            term: "SOS reconstruction handles a single square `ℓ*ℓ < 0` of a ±1-coefficient \
                   linear form ℓ, the two-variable AM-GM sum form `x²+y²−2xy < 0`, any query \
                   whose SOS certificate is a single perfect square, a SUM of ±1-unit \
                   squares (every d=1, zero affine), and a RATIONAL-weight sum of squares \
                   (denominator-cleared); higher-degree / nonzero-affine SOS is a later slice"
                .to_owned(),
        });
    };

    // Map the repeated linear factor `ℓ` to its `R`-typed kernel term (the same
    // faithful encoding the LRA reconstruction trusts; the bare-variable case
    // `ℓ = x` collapses to a single `var_const`). `sq_nonneg` is ∀-valid, so it
    // discharges `0 ≤ ℓ·ℓ` for this `ℓ` regardless of its sign.
    let lin = real_to_lin(arena, factor).ok_or_else(|| ReconstructError::UnsupportedTerm {
        term: "SOS single-square factor is not a linear form".to_owned(),
    })?;
    let ell = ctx.lin_to_r(&lin)?;
    let zero = ctx.mk_zero();
    let xx = ctx.mk_mul(ell, ell);

    // 1. sq : le zero (mul ℓ ℓ)  :=  sq_nonneg ℓ.
    let sq = {
        let sq_nonneg_name = ctx.arith().sq_nonneg;
        let sq_nonneg = ctx.kernel_mut().const_(sq_nonneg_name, vec![]);
        ctx.kernel_mut().app(sq_nonneg, ell)
    };

    // 2. hlt : lt (mul ℓ ℓ) zero — the asserted atom `ℓ*ℓ < 0` as a hypothesis.
    let hlt = {
        let prop = ctx.mk_lt(xx, zero);
        ctx.hyp_axiom(prop)?
    };

    // 3. chain : lt zero zero  :=  lt_of_le_of_lt zero (mul ℓ ℓ) zero sq hlt.
    let chain = {
        let ax_name = ctx.arith().lt_of_le_of_lt;
        let ax = ctx.kernel_mut().const_(ax_name, vec![]);
        let e = ctx.kernel_mut().app(ax, zero);
        let e = ctx.kernel_mut().app(e, xx);
        let e = ctx.kernel_mut().app(e, zero);
        let e = ctx.kernel_mut().app(e, sq);
        ctx.kernel_mut().app(e, hlt)
    };

    // 4. bad : False  :=  lt_irrefl zero chain.
    let proof = {
        let irrefl_name = ctx.arith().lt_irrefl;
        let irrefl = ctx.kernel_mut().const_(irrefl_name, vec![]);
        let e = ctx.kernel_mut().app(irrefl, zero);
        ctx.kernel_mut().app(e, chain)
    };

    // Soundness gate: the assembled term must kernel-infer to `False`.
    let inferred = ctx
        .kernel_mut()
        .infer(proof)
        .map_err(|e| ReconstructError::KernelRejected {
            rule: "sos_single_square".to_owned(),
            detail: format!("SOS infer failed: {e:?}"),
        })?;
    let false_ = {
        let f = ctx.arith().logic.false_;
        ctx.kernel_mut().const_(f, vec![])
    };
    if ctx.kernel_mut().def_eq(inferred, false_) {
        Ok(proof)
    } else {
        Err(ReconstructError::KernelRejected {
            rule: "sos_single_square".to_owned(),
            detail: "SOS single-square refutation did not infer to False".to_owned(),
        })
    }
}

/// Reconstruct the degree-2 two-variable **AM-GM sum form** `x²+y²−2xy < 0` to a
/// kernel-checked `False` (ADR-0040, the first SOS shape needing the ring
/// normalizer). The asserted lhs is a *sum of monomials*, not a literal `ℓ·ℓ`,
/// so the crux is a kernel-proven ring identity `Eq R p ((x−y)·(x−y))` over which
/// square-nonnegativity is transported.
///
/// Variable symbols are mapped deterministically: `sx → index 0`, `sy → index 1`.
/// The faithful kernel encoding of the asserted lhs `RealSub(A, B)` is
/// `pK = add A (neg B)` with `A = add (mul x x)(mul y y)` and
/// `B = add (mul x y)(mul x y)` — denotationally `x² + y² − 2xy`.
///
/// The reconstruction:
/// 1. builds `pK`, `ellK = add x (neg y)`, `sqK = mul ellK ellK`;
/// 2. proves the ring identity `idK : Eq R pK sqK` (the crux, via
///    [`LraReconstructCtx`]'s additive+multiplicative `Eq R` engine);
/// 3. `sq : le zero sqK := sq_nonneg ellK`;
/// 4. transports nonnegativity back along `idK` to `lep : le zero pK`;
/// 5. closes `lt_of_le_of_lt 0 pK 0 lep hlt : lt 0 0` (with `hlt : lt pK 0` the
///    asserted atom) and refutes it with `lt_irrefl 0`.
///
/// Kernel-gated: the assembled term must `infer` to `False`.
#[allow(clippy::too_many_lines)]
fn reconstruct_am_gm_two_var(
    ctx: &mut LraReconstructCtx,
    _sx: axeyum_ir::SymbolId,
    _sy: axeyum_ir::SymbolId,
) -> Result<ExprId, ReconstructError> {
    // --- kernel atoms --------------------------------------------------------
    let xk = {
        let n = ctx.var_const(0);
        ctx.kernel_mut().const_(n, vec![])
    };
    let yk = {
        let n = ctx.var_const(1);
        ctx.kernel_mut().const_(n, vec![])
    };
    let nyk = ctx.mk_neg(yk);
    let ell = ctx.mk_add(xk, nyk); // x + (-y) = x − y
    let sqk = ctx.mk_mul(ell, ell); // (x−y)·(x−y)

    // Monomial atoms.
    let xx = ctx.mk_mul(xk, xk); // x·x
    let yy = ctx.mk_mul(yk, yk); // y·y
    let xy = ctx.mk_mul(xk, yk); // x·y
    let nxy = ctx.mk_neg(xy); // −(x·y)

    // pK = add (add xx yy) (neg (add xy xy)) — faithful `x²+y²−(xy+xy)`.
    let xx_yy = ctx.mk_add(xx, yy);
    let xy_xy = ctx.mk_add(xy, xy);
    let neg_xy_xy = ctx.mk_neg(xy_xy);
    let pk = ctx.mk_add(xx_yy, neg_xy_xy);

    // Canonical join target S = add xx (add yy (add nxy nxy)).
    let nxy_nxy = ctx.mk_add(nxy, nxy);
    let yy_tail = ctx.mk_add(yy, nxy_nxy);
    let s = ctx.mk_add(xx, yy_tail);

    // --- pK → S (purely additive) -------------------------------------------
    // step1: neg(add xy xy) ⟶ add nxy nxy  (lift neg over the inner add).
    let neg_add = ctx.neg_add_eq(xy, xy); // neg(xy+xy) = (-xy)+(-xy)
    let p_step1 = ctx.congr_add_right(xx_yy, neg_xy_xy, nxy_nxy, neg_add);
    // p1 = add (add xx yy) (add nxy nxy).
    let p1 = ctx.mk_add(xx_yy, nxy_nxy);
    // step2: reassociate (xx+yy)+(nxy+nxy) ⟶ xx+(yy+(nxy+nxy)) = S.
    let p_step2 = ctx.add_assoc_eq(xx, yy, nxy_nxy); // (xx+yy)+T = xx+(yy+T)
    let pk_to_s = ctx.eq_trans_r(pk, p1, s, p_step1, p_step2);

    // --- sqK → S (the ring expansion) ---------------------------------------
    // d1: mul ell ell = add (mul ell x)(mul ell (neg y))  (left_distrib on the
    // right operand ell = add x (neg y); `mul ell ell` IS `mul ell (add x (neg y))`).
    let a_term = ctx.mk_mul(ell, xk); // mul ell x
    let b_term = ctx.mk_mul(ell, nyk); // mul ell (neg y)
    let e1 = ctx.mk_add(a_term, b_term);
    let d1 = ctx.left_distrib_eq(ell, xk, nyk); // sqK = add A B

    // A = mul ell x ⟶ add xx nxy.
    let a_eq = {
        // mul (x+(-y)) x =[mul_comm] mul x (x+(-y))
        let comm = ctx.mul_comm_eq(ell, xk); // mul ell x = mul x ell
        let x_ell = ctx.mk_mul(xk, ell); // mul x (x+(-y))
        // mul x (x+(-y)) =[left_distrib] add (mul x x)(mul x (neg y)) = add xx (mul x (neg y))
        let ld = ctx.left_distrib_eq(xk, xk, nyk);
        let x_ny = ctx.mk_mul(xk, nyk); // mul x (neg y)
        let xx_xny = ctx.mk_add(xx, x_ny); // add xx (mul x (neg y))
        let comm_ld = ctx.eq_trans_r(a_term, x_ell, xx_xny, comm, ld);
        // mul x (neg y) =[mul_neg_right] neg (mul x y) = nxy.
        let mnr = ctx.mul_neg_right_eq(xk, yk); // mul x (neg y) = neg (x·y)
        let xx_nxy = ctx.mk_add(xx, nxy);
        let cong = ctx.congr_add_right(xx, x_ny, nxy, mnr); // add xx (x·(-y)) = add xx nxy
        ctx.eq_trans_r(a_term, xx_xny, xx_nxy, comm_ld, cong)
    };
    let xx_nxy = ctx.mk_add(xx, nxy);

    // B = mul ell (neg y) ⟶ add nxy yy.
    let b_eq = {
        // mul (x+(-y)) (neg y) =[mul_comm] mul (neg y) (x+(-y))
        let comm = ctx.mul_comm_eq(ell, nyk); // mul ell (neg y) = mul (neg y) ell
        let ny_ell = ctx.mk_mul(nyk, ell);
        // mul (neg y) (x+(-y)) =[left_distrib] add (mul (neg y) x)(mul (neg y)(neg y))
        let ld = ctx.left_distrib_eq(nyk, xk, nyk);
        let ny_x = ctx.mk_mul(nyk, xk); // mul (neg y) x
        let ny_ny = ctx.mk_mul(nyk, nyk); // mul (neg y)(neg y)
        let ny_x_plus = ctx.mk_add(ny_x, ny_ny);
        let comm_ld = ctx.eq_trans_r(b_term, ny_ell, ny_x_plus, comm, ld);
        // mul (neg y) x =[mul_neg_left] neg (mul y x) =[congr_neg mul_comm] neg (mul x y) = nxy.
        let mnl = ctx.mul_neg_left_eq(yk, xk); // mul (neg y) x = neg (y·x)
        let yx = ctx.mk_mul(yk, xk);
        let neg_yx = ctx.mk_neg(yx);
        let comm_yx = ctx.mul_comm_eq(yk, xk); // y·x = x·y
        let cong_neg = ctx.congr_neg(yx, xy, comm_yx); // neg(y·x) = neg(x·y) = nxy
        let ny_x_to_nxy = ctx.eq_trans_r(ny_x, neg_yx, nxy, mnl, cong_neg);
        // mul (neg y)(neg y) =[neg_mul_neg] mul y y = yy.
        let nmn = ctx.neg_mul_neg_eq(yk, yk); // (neg y)(neg y) = y·y = yy
        // congr both sides of `add (mul (neg y) x)(mul (neg y)(neg y))`.
        let nxy_plus = ctx.mk_add(nxy, ny_ny);
        let cong_l = ctx.congr_add_left(ny_x, nxy, ny_ny, ny_x_to_nxy);
        let nxy_yy = ctx.mk_add(nxy, yy);
        let cong_r = ctx.congr_add_right(nxy, ny_ny, yy, nmn);
        let cong_both = ctx.eq_trans_r(ny_x_plus, nxy_plus, nxy_yy, cong_l, cong_r);
        ctx.eq_trans_r(b_term, ny_x_plus, nxy_yy, comm_ld, cong_both)
    };
    let nxy_yy = ctx.mk_add(nxy, yy);

    // E1 = add A B ⟶ E2 = add (add xx nxy)(add nxy yy) (congr both sides).
    let e2 = ctx.mk_add(xx_nxy, nxy_yy);
    let e1_to_e2 = {
        let cong_l = ctx.congr_add_left(a_term, xx_nxy, b_term, a_eq);
        let mid = ctx.mk_add(xx_nxy, b_term);
        let cong_r = ctx.congr_add_right(xx_nxy, b_term, nxy_yy, b_eq);
        ctx.eq_trans_r(e1, mid, e2, cong_l, cong_r)
    };

    // E2 = (xx+nxy)+(nxy+yy) ⟶ S = xx+(yy+(nxy+nxy)).
    let e2_to_s = {
        // assoc: (xx+nxy)+(nxy+yy) = xx + (nxy + (nxy+yy)).
        let assoc = ctx.add_assoc_eq(xx, nxy, nxy_yy);
        let nxy_nxyyy = ctx.mk_add(nxy, nxy_yy); // nxy + (nxy + yy)
        let m1 = ctx.mk_add(xx, nxy_nxyyy); // xx + (nxy+(nxy+yy))
        // tail reorder: nxy+(nxy+yy) ⟶ (nxy+nxy)+yy ⟶ yy+(nxy+nxy).
        let assoc_tail = ctx.add_assoc_eq(nxy, nxy, yy); // (nxy+nxy)+yy = nxy+(nxy+yy)
        let nxynxy_yy = ctx.mk_add(nxy_nxy, yy); // (nxy+nxy)+yy
        let tail1 = ctx.eq_symm_r(nxynxy_yy, nxy_nxyyy, assoc_tail); // nxy+(nxy+yy) = (nxy+nxy)+yy
        let comm_tail = ctx.add_comm_eq(nxy_nxy, yy); // (nxy+nxy)+yy = yy+(nxy+nxy)
        let tail_eq = ctx.eq_trans_r(nxy_nxyyy, nxynxy_yy, yy_tail, tail1, comm_tail);
        // lift into xx + _ : m1 ⟶ S.
        let lift = ctx.congr_add_right(xx, nxy_nxyyy, yy_tail, tail_eq);
        ctx.eq_trans_r(e2, m1, s, assoc, lift)
    };

    // sqK ⟶ E1 ⟶ E2 ⟶ S.
    let sq_to_e2 = ctx.eq_trans_r(sqk, e1, e2, d1, e1_to_e2);
    let sqk_to_s = ctx.eq_trans_r(sqk, e2, s, sq_to_e2, e2_to_s);

    // --- idK : Eq R pK sqK  ⟵  trans (pK→S) (symm sqK→S) --------------------
    let s_to_sqk = ctx.eq_symm_r(sqk, s, sqk_to_s); // S = sqK
    let idk = ctx.eq_trans_r(pk, s, sqk, pk_to_s, s_to_sqk);

    // --- nonnegativity + order chain ----------------------------------------
    let zero = ctx.mk_zero();
    // sq : le zero sqK := sq_nonneg ell.
    let sq = {
        let sq_nonneg_name = ctx.arith().sq_nonneg;
        let sq_nonneg = ctx.kernel_mut().const_(sq_nonneg_name, vec![]);
        ctx.kernel_mut().app(sq_nonneg, ell)
    };
    // lep : le zero pK — transport `sq` backwards along idK (rewrite sqK ⟶ pK,
    // i.e. cast the right operand of `le zero _` along symm idK : Eq R sqK pK).
    let id_sym = ctx.eq_symm_r(pk, sqk, idk); // Eq R sqK pK
    let lep = ctx.le_cast_right(zero, sqk, pk, sq, id_sym);

    // hlt : lt pK zero — the asserted atom `p < 0`.
    let hlt = {
        let prop = ctx.mk_lt(pk, zero);
        ctx.hyp_axiom(prop)?
    };

    // chain : lt zero zero := lt_of_le_of_lt zero pK zero lep hlt.
    let chain = {
        let ax_name = ctx.arith().lt_of_le_of_lt;
        let ax = ctx.kernel_mut().const_(ax_name, vec![]);
        let e = ctx.kernel_mut().app(ax, zero);
        let e = ctx.kernel_mut().app(e, pk);
        let e = ctx.kernel_mut().app(e, zero);
        let e = ctx.kernel_mut().app(e, lep);
        ctx.kernel_mut().app(e, hlt)
    };
    // bad : False := lt_irrefl zero chain.
    let proof = {
        let irrefl_name = ctx.arith().lt_irrefl;
        let irrefl = ctx.kernel_mut().const_(irrefl_name, vec![]);
        let e = ctx.kernel_mut().app(irrefl, zero);
        ctx.kernel_mut().app(e, chain)
    };

    // Soundness gate: the assembled term must kernel-infer to `False`.
    let inferred = ctx
        .kernel_mut()
        .infer(proof)
        .map_err(|e| ReconstructError::KernelRejected {
            rule: "sos_am_gm_two_var".to_owned(),
            detail: format!("AM-GM SOS infer failed: {e:?}"),
        })?;
    let false_ = {
        let f = ctx.arith().logic.false_;
        ctx.kernel_mut().const_(f, vec![])
    };
    if ctx.kernel_mut().def_eq(inferred, false_) {
        Ok(proof)
    } else {
        Err(ReconstructError::KernelRejected {
            rule: "sos_am_gm_two_var".to_owned(),
            detail: "AM-GM SOS refutation did not infer to False".to_owned(),
        })
    }
}

/// Maximum integer coefficient magnitude the SOS-certificate reconstructor expands
/// into repeated monomial generators. `ℓ²` of a ±1-linear form has coefficients in
/// `{−2, −1, 0, 1, 2}` (the cross term `2xᵢxⱼ`), so a small bound suffices; a larger
/// one would only inflate proof size. Outside this bound we decline.
const SOS_MAX_COEFF: i128 = 16;

/// Build the [`RExpr`] for the certificate polynomial term `(factors, coeff)`'s
/// monomial (ignoring the sign/magnitude of `coeff`): a [`RExpr::One`] for the
/// constant, a [`RExpr::Var`] for a linear term, a [`RExpr::Mul`] of two vars for a
/// quadratic term, and a `Var·Var` for a square (`xᵢ²`). Returns `None` (decline)
/// for any factor of total degree ≥ 3 or an out-of-range/malformed shape.
fn cert_mono_to_rexpr(factors: &[(usize, u32)], n_vars: usize) -> Option<RExpr> {
    match factors {
        [] => Some(RExpr::One),
        [(i, 1)] if *i < n_vars => Some(RExpr::Var(*i)),
        [(i, 2)] if *i < n_vars => Some(RExpr::Mul(
            Box::new(RExpr::Var(*i)),
            Box::new(RExpr::Var(*i)),
        )),
        [(i, 1), (j, 1)] if *i < n_vars && *j < n_vars => Some(RExpr::Mul(
            Box::new(RExpr::Var(*i)),
            Box::new(RExpr::Var(*j)),
        )),
        _ => None,
    }
}

/// Build the [`RExpr`] for the **asserted polynomial** `p` from the certificate's
/// indexed monomials: a left-nested `add` over `coeff`-many copies of each monomial
/// (sign-adjusted), in the certificate's deterministic `BTreeMap` order. The result
/// is a faithful kernel encoding of `p` over canonical indices `var_const(i)` (the
/// SAME indices `ellK` uses). `None` (decline) on a non-integer coefficient, a
/// coefficient exceeding [`SOS_MAX_COEFF`] in magnitude, a degree-≥3 monomial, or an
/// empty polynomial.
fn cert_poly_to_rexpr(terms: &[(Vec<(usize, u32)>, Rational)], n_vars: usize) -> Option<RExpr> {
    let mut atoms: Vec<RExpr> = Vec::new();
    for (factors, coeff) in terms {
        if coeff.denominator() != 1 {
            return None; // non-integer coefficient — outside this slice
        }
        let c = coeff.numerator();
        if c == 0 {
            continue;
        }
        if c.abs() > SOS_MAX_COEFF {
            return None; // coefficient too large to expand into unit monomials
        }
        let base = cert_mono_to_rexpr(factors, n_vars)?;
        let count = c.unsigned_abs();
        for _ in 0..count {
            let term = if c < 0 {
                RExpr::Neg(Box::new(base.clone()))
            } else {
                base.clone()
            };
            atoms.push(term);
        }
    }
    let mut iter = atoms.into_iter();
    let first = iter.next()?; // empty ⇒ decline (no atom to refute)
    let mut acc = first;
    for t in iter {
        acc = RExpr::Add(Box::new(acc), Box::new(t));
    }
    Some(acc)
}

/// Build the [`RExpr`] for the single square `ℓ = Σⱼ cⱼ·xⱼ` from its signed unit
/// coefficients (each `±1`): a left-nested `add` over `xⱼ` / `neg xⱼ`. `cⱼ` are
/// over the same canonical indices as [`cert_poly_to_rexpr`].
fn cert_square_to_rexpr(coeffs: &[(usize, i128)]) -> Option<RExpr> {
    let mut iter = coeffs.iter().map(|&(idx, c)| {
        if c < 0 {
            RExpr::Neg(Box::new(RExpr::Var(idx)))
        } else {
            RExpr::Var(idx)
        }
    });
    let first = iter.next()?;
    let mut acc = first;
    for t in iter {
        acc = RExpr::Add(Box::new(acc), Box::new(t));
    }
    Some(acc)
}

/// Reconstruct, **from the SOS certificate**, any strict query `p < 0` whose
/// certificate is a SINGLE perfect square of a ±1-coefficient linear form
/// `ℓ = Σⱼ ±xⱼ` (with `d = 1` and a zero affine row). Generalizes
/// [`reconstruct_am_gm_two_var`] off the hard-coded `(x−y)²` shape via the degree-2
/// ring normalizer ([`LraReconstructCtx::normalize_deg2`]).
///
/// Returns:
/// - `Ok(Some(proof))` — a kernel-checked `False` (gated by `infer` + `def_eq`).
/// - `Ok(None)` — the certificate is not a single ±1-unit square (decline; the
///   caller falls through), or building `pK`/`ellK` hit this slice's bounds.
/// - `Err(_)` — only a genuine kernel rejection (a buggy normalizer would surface
///   here, never an unsound `False`).
///
/// The crux is the ring identity `idK : Eq R pK sqK`, assembled as
/// `trans (normalize pK) (symm (normalize sqK))` **after** confirming the two
/// normal forms are identical — which the certificate guarantees (`p = ℓ²` over ℚ)
/// but this function re-checks, declining if they disagree rather than fabricating.
fn reconstruct_sos_single_unit_square(
    ctx: &mut LraReconstructCtx,
    arena: &TermArena,
    assertions: &[TermId],
) -> Result<Option<ExprId>, ReconstructError> {
    // Obtain the self-checked SOS certificate of the (conjunction of) assertion(s).
    let Some(cert) = crate::nra_real_root::sos_refute_with_certificate(arena, assertions) else {
        return Ok(None);
    };
    // This slice handles only the `p < 0` (M PSD) atom shape, as a single ±1 square.
    if !cert.strict_lt() {
        return Ok(None);
    }
    let Some(square_coeffs) = cert.single_unit_square() else {
        return Ok(None);
    };
    let n_vars = cert.n_vars();

    // Build pK (faithful encoding of the asserted polynomial p) and ellK (the square
    // root ℓ), both over the SAME canonical indices. `sqK = mul ellK ellK`.
    let Some(p_rexpr) = cert_poly_to_rexpr(cert.poly_terms(), n_vars) else {
        return Ok(None);
    };
    let Some(ell_rexpr) = cert_square_to_rexpr(&square_coeffs) else {
        return Ok(None);
    };
    let sq_rexpr = RExpr::Mul(Box::new(ell_rexpr.clone()), Box::new(ell_rexpr.clone()));

    // Normalize both to canonical signed-monomial sums, each with its Eq-proof.
    let Some((p_gens, pk, p_to_canon)) = ctx.normalize_deg2(&p_rexpr) else {
        return Ok(None);
    };
    let Some((sq_gens, sqk, sq_to_canon)) = ctx.normalize_deg2(&sq_rexpr) else {
        return Ok(None);
    };

    // Re-check the certificate's promise `p = ℓ²` at the canonical-form level: the
    // two normal forms MUST be identical (the normalizer sorts deterministically, so
    // equal multisets of monomials ⇒ identical gen vectors). If they disagree, the
    // certificate/normalizer is not what we think — decline, never fabricate `idK`.
    if p_gens != sq_gens {
        return Ok(None);
    }

    // idK : Eq R pK sqK := trans (pK → canon) (symm (sqK → canon)).
    let canon = ctx.mono_gens_to_expr(&p_gens);
    let canon_to_sq = ctx.eq_symm_r(sqk, canon, sq_to_canon); // Eq R canon sqK
    let idk = ctx.eq_trans_r(pk, canon, sqk, p_to_canon, canon_to_sq); // Eq R pK sqK

    // Nonnegativity + order chain (mirrors `reconstruct_am_gm_two_var`).
    // ellK is the `mul` LHS/RHS of sqK; emit it directly (same hash-consed ExprId).
    let ell = ctx.emit_rexpr(&ell_rexpr);
    let zero = ctx.mk_zero();
    // sq : le zero sqK := sq_nonneg ell. (sqK = mul ell ell faithfully.)
    let sq = {
        let sq_nonneg_name = ctx.arith().sq_nonneg;
        let sq_nonneg = ctx.kernel_mut().const_(sq_nonneg_name, vec![]);
        ctx.kernel_mut().app(sq_nonneg, ell)
    };
    // lep : le zero pK — transport `sq` backward along symm idK (rewrite sqK ⟶ pK).
    let id_sym = ctx.eq_symm_r(pk, sqk, idk); // Eq R sqK pK
    let lep = ctx.le_cast_right(zero, sqk, pk, sq, id_sym);
    // hlt : lt pK zero — the asserted atom `p < 0`.
    let hlt = {
        let prop = ctx.mk_lt(pk, zero);
        ctx.hyp_axiom(prop)?
    };
    // chain : lt zero zero := lt_of_le_of_lt zero pK zero lep hlt.
    let chain = {
        let ax_name = ctx.arith().lt_of_le_of_lt;
        let ax = ctx.kernel_mut().const_(ax_name, vec![]);
        let e = ctx.kernel_mut().app(ax, zero);
        let e = ctx.kernel_mut().app(e, pk);
        let e = ctx.kernel_mut().app(e, zero);
        let e = ctx.kernel_mut().app(e, lep);
        ctx.kernel_mut().app(e, hlt)
    };
    // bad : False := lt_irrefl zero chain.
    let proof = {
        let irrefl_name = ctx.arith().lt_irrefl;
        let irrefl = ctx.kernel_mut().const_(irrefl_name, vec![]);
        let e = ctx.kernel_mut().app(irrefl, zero);
        ctx.kernel_mut().app(e, chain)
    };

    // Soundness gate: the assembled term must kernel-infer to `False`. A buggy
    // normalizer makes this fail (KernelRejected), never an accepted unsound proof.
    let inferred = ctx
        .kernel_mut()
        .infer(proof)
        .map_err(|e| ReconstructError::KernelRejected {
            rule: "sos_single_unit_square".to_owned(),
            detail: format!("SOS certificate infer failed: {e:?}"),
        })?;
    let false_ = {
        let f = ctx.arith().logic.false_;
        ctx.kernel_mut().const_(f, vec![])
    };
    if ctx.kernel_mut().def_eq(inferred, false_) {
        Ok(Some(proof))
    } else {
        Err(ReconstructError::KernelRejected {
            rule: "sos_single_unit_square".to_owned(),
            detail: "SOS certificate refutation did not infer to False".to_owned(),
        })
    }
}

/// Reconstruct, **from the SOS certificate**, any strict query `p < 0` whose
/// certificate is a **SUM of perfect squares** of ±1-coefficient linear forms
/// `ℓ₁..ℓₘ` (every `D[k] = 1`, zero affine row). Generalizes
/// [`reconstruct_sos_single_unit_square`] (the `m = 1` case) by folding
/// square-nonnegativity over several squares.
///
/// Returns:
/// - `Ok(Some(proof))` — a kernel-checked `False` (gated by `infer` + `def_eq`).
/// - `Ok(None)` — the certificate is not a sum of ±1-unit squares (decline; the
///   caller falls through), or building the kernel terms hit this slice's bounds,
///   or the two normal forms disagree (never fabricate the ring identity).
/// - `Err(_)` — only a genuine kernel rejection.
///
/// Construction:
/// - `sosK = add (ℓ₁·ℓ₁) (add (ℓ₂·ℓ₂) (… (ℓₘ·ℓₘ)))` — a RIGHT-nested `add` of the
///   squares with the last square as the innermost leaf (NO trailing zero, so the
///   kernel `sosK` is exactly the faithful encoding the normalizer returns).
/// - `idK : Eq R pK sosK := trans (normalize pK) (symm (normalize sosK))`, only
///   after confirming the canonical gens are identical (else decline).
/// - `nn : le zero sosK` folds from the innermost (last) square outward. Base case
///   (the `m`-th square): `sq_nonneg ℓₘ : le zero (ℓₘ·ℓₘ)`. Then for each earlier
///   square `ℓₖ` (k = m-1 … 1) combine `sq_nonneg ℓₖ : le zero (ℓₖ·ℓₖ)` with the
///   running `le zero tail` via
///   `add_le_add zero (ℓₖ·ℓₖ) zero tail … : le (add zero zero)(add (ℓₖ·ℓₖ) tail)`,
///   then cast the lhs `add zero zero → zero` (`add_zero zero`) so the type stays
///   `le zero (add (ℓₖ·ℓₖ) tail)` — matching `sosK`'s exact right-nesting.
/// - transport `nn` along `idK` to `lep : le zero pK`, then `lt_of_le_of_lt` with
///   the asserted `hlt : lt pK zero` ⇒ `lt zero zero`, refuted by `lt_irrefl zero`.
#[allow(clippy::too_many_lines)]
fn reconstruct_sos_multi_unit_square(
    ctx: &mut LraReconstructCtx,
    arena: &TermArena,
    assertions: &[TermId],
) -> Result<Option<ExprId>, ReconstructError> {
    let Some(cert) = crate::nra_real_root::sos_refute_with_certificate(arena, assertions) else {
        return Ok(None);
    };
    if !cert.strict_lt() {
        return Ok(None);
    }
    let Some(squares) = cert.unit_squares() else {
        return Ok(None);
    };
    let n_vars = cert.n_vars();

    // Faithful encoding of the asserted polynomial p.
    let Some(p_rexpr) = cert_poly_to_rexpr(cert.poly_terms(), n_vars) else {
        return Ok(None);
    };

    // Per-square: the linear form ℓₖ as an RExpr (for emit) and the square sub-RExpr
    // (ℓₖ·ℓₖ).
    let mut ell_rexprs: Vec<RExpr> = Vec::with_capacity(squares.len());
    let mut sq_rexprs: Vec<RExpr> = Vec::with_capacity(squares.len());
    for sq_coeffs in &squares {
        let Some(ell) = cert_square_to_rexpr(sq_coeffs) else {
            return Ok(None);
        };
        sq_rexprs.push(RExpr::Mul(Box::new(ell.clone()), Box::new(ell.clone())));
        ell_rexprs.push(ell);
    }

    // sosK as an RExpr: RIGHT-nested add over the squares, last square as the
    // innermost LEAF (no trailing zero). E.g. for m=3:
    //   add sq_0 (add sq_1 sq_2).
    // The kernel `sosK` is then EXACTLY the faithful encoding `normalize_deg2`
    // returns for this RExpr, so no bridge between the fold's `sosK` and the
    // normalized form is needed.
    let Some((last, init)) = sq_rexprs.split_last() else {
        return Ok(None);
    };
    let mut sos_rexpr = last.clone();
    for r in init.iter().rev() {
        sos_rexpr = RExpr::Add(Box::new(r.clone()), Box::new(sos_rexpr));
    }

    // Normalize p and the SOS sum; the canonical gens MUST agree (else decline).
    let Some((p_gens, pk, p_to_canon)) = ctx.normalize_deg2(&p_rexpr) else {
        return Ok(None);
    };
    let Some((sos_gens, sosk, sos_to_canon)) = ctx.normalize_deg2(&sos_rexpr) else {
        return Ok(None);
    };
    if p_gens != sos_gens {
        return Ok(None);
    }

    // idK : Eq R pK sosK := trans (pK → canon)(symm (sosK → canon)).
    let canon = ctx.mono_gens_to_expr(&p_gens);
    let canon_to_sos = ctx.eq_symm_r(sosk, canon, sos_to_canon); // Eq R canon sosK
    let idk = ctx.eq_trans_r(pk, canon, sosk, p_to_canon, canon_to_sos); // Eq R pK sosK

    // Kernel-level per-square ℓₖ and (ℓₖ·ℓₖ), emitted from the SAME RExprs so the
    // `mul`/`add` ExprIds are hash-consed identical to those inside `sosK`.
    let zero = ctx.mk_zero();
    let mut ells: Vec<ExprId> = Vec::with_capacity(squares.len());
    let mut sqs: Vec<ExprId> = Vec::with_capacity(squares.len());
    for ell_rexpr in &ell_rexprs {
        let ell = ctx.emit_rexpr(ell_rexpr);
        ells.push(ell);
        sqs.push(ctx.mk_mul(ell, ell));
    }

    // -------------------------------------------------------------------------
    // Nonnegativity fold: nn : le zero sosK, where
    //   sosK = add sq_0 (add sq_1 (… sq_{m-1})).  (right-nested, last = leaf)
    // Base: the LAST square's sq_nonneg gives `le zero sq_{m-1}`. Then fold the
    // earlier squares FROM LAST-1 DOWN TO FIRST, each step prepending one square to
    // the running `le zero tail`, casting `add zero zero → zero` on the lhs.
    // -------------------------------------------------------------------------
    let m = sqs.len();
    let sq_nonneg_of = |ctx: &mut LraReconstructCtx, ell: ExprId| -> ExprId {
        let name = ctx.arith().sq_nonneg;
        let f = ctx.kernel_mut().const_(name, vec![]);
        ctx.kernel_mut().app(f, ell) // le zero (mul ell ell)
    };
    // Base: nn : le zero sq_{m-1}.
    let mut nn = sq_nonneg_of(ctx, ells[m - 1]);
    let mut tail = sqs[m - 1]; // running right-nested tail (matches sosK structurally)
    for idx in (0..m - 1).rev() {
        let sq = sqs[idx];
        // sq_k : le zero (mul ℓ ℓ).
        let sq_k = sq_nonneg_of(ctx, ells[idx]);
        // add_le_add zero (mul ℓ ℓ) zero tail sq_k nn
        //   : le (add zero zero)(add (mul ℓ ℓ) tail).
        let combined = ctx.add_le_add_app(zero, sq, zero, tail, sq_k, nn);
        // Cast lhs (add zero zero) → zero via add_zero zero : Eq R (add zero zero) zero.
        let new_tail = ctx.mk_add(sq, tail); // add (mul ℓ ℓ) tail (= next sosK prefix)
        let lhs = ctx.mk_add(zero, zero);
        let add_zero_zero = ctx.add_zero_eq(zero); // Eq R (add zero zero) zero
        nn = ctx.le_cast_left(lhs, zero, new_tail, combined, add_zero_zero);
        // now nn : le zero (add (mul ℓ ℓ) tail) = le zero new_tail.
        tail = new_tail;
    }
    // nn : le zero sosK (= le zero tail, tail == sosk structurally).
    debug_assert_eq!(tail, sosk);

    // Transport nn backward along idK (rewrite sosK → pK) ⇒ lep : le zero pK.
    let id_sym = ctx.eq_symm_r(pk, sosk, idk); // Eq R sosK pK
    let lep = ctx.le_cast_right(zero, sosk, pk, nn, id_sym);

    // hlt : lt pK zero — the asserted atom `p < 0`.
    let hlt = {
        let prop = ctx.mk_lt(pk, zero);
        ctx.hyp_axiom(prop)?
    };
    // chain : lt zero zero := lt_of_le_of_lt zero pK zero lep hlt.
    let chain = {
        let ax_name = ctx.arith().lt_of_le_of_lt;
        let ax = ctx.kernel_mut().const_(ax_name, vec![]);
        let e = ctx.kernel_mut().app(ax, zero);
        let e = ctx.kernel_mut().app(e, pk);
        let e = ctx.kernel_mut().app(e, zero);
        let e = ctx.kernel_mut().app(e, lep);
        ctx.kernel_mut().app(e, hlt)
    };
    // bad : False := lt_irrefl zero chain.
    let proof = {
        let irrefl_name = ctx.arith().lt_irrefl;
        let irrefl = ctx.kernel_mut().const_(irrefl_name, vec![]);
        let e = ctx.kernel_mut().app(irrefl, zero);
        ctx.kernel_mut().app(e, chain)
    };

    // Soundness gate.
    let inferred = ctx
        .kernel_mut()
        .infer(proof)
        .map_err(|e| ReconstructError::KernelRejected {
            rule: "sos_multi_unit_square".to_owned(),
            detail: format!("SOS multi-square certificate infer failed: {e:?}"),
        })?;
    let false_ = {
        let f = ctx.arith().logic.false_;
        ctx.kernel_mut().const_(f, vec![])
    };
    if ctx.kernel_mut().def_eq(inferred, false_) {
        Ok(Some(proof))
    } else {
        Err(ReconstructError::KernelRejected {
            rule: "sos_multi_unit_square".to_owned(),
            detail: "SOS multi-square refutation did not infer to False".to_owned(),
        })
    }
}

/// Upper bound on the cleared denominator `M` and on any integer linear-form
/// coefficient the rational-weight SOS reconstructor will expand into repeated unit
/// monomials / repeated squares (the proof is linear in these magnitudes, so a large
/// value is declined — `Ok(None)` — rather than building a giant kernel term).
const SOS_RATIONAL_MAX: i128 = 64;

/// The least common multiple of `a` and `b` (both already nonnegative), returning
/// `None` on `i128` overflow. `lcm(0, _) = lcm(_, 0) = 0` is never needed here (all
/// denominators are ≥ 1), but `a = 0` is handled as the identity for folding.
fn checked_lcm(a: i128, b: i128) -> Option<i128> {
    if a == 0 {
        return Some(b);
    }
    if b == 0 {
        return Some(a);
    }
    let g = gcd_i128(a, b);
    // a / g is exact; multiply by b.
    (a / g).checked_mul(b)
}

/// Build the [`RExpr`] for an INTEGER-coefficient linear form `ℓ⁺ = Σⱼ cⱼ·xⱼ` from
/// signed coefficients `cⱼ` (any nonzero integer, not just ±1): a left-nested `add`
/// over `|cⱼ|` repeated copies of `xⱼ` (or `neg xⱼ` when `cⱼ < 0`). E.g.
/// `2x₀ − x₁` ⇒ `add (add x₀ x₀) (neg x₁)`. `None` (decline) on an empty list or any
/// `|cⱼ| > SOS_RATIONAL_MAX`.
fn int_lin_to_rexpr(coeffs: &[(usize, i128)]) -> Option<RExpr> {
    let mut atoms: Vec<RExpr> = Vec::new();
    for &(idx, c) in coeffs {
        if c == 0 {
            continue;
        }
        if c.unsigned_abs() > SOS_RATIONAL_MAX as u128 {
            return None; // coefficient too large to expand into unit copies
        }
        let count = c.unsigned_abs();
        for _ in 0..count {
            let atom = if c < 0 {
                RExpr::Neg(Box::new(RExpr::Var(idx)))
            } else {
                RExpr::Var(idx)
            };
            atoms.push(atom);
        }
    }
    let mut iter = atoms.into_iter();
    let first = iter.next()?;
    let mut acc = first;
    for t in iter {
        acc = RExpr::Add(Box::new(acc), Box::new(t));
    }
    Some(acc)
}

/// From the certificate's rational SOS decomposition `p = Σₖ dₖ·ℓₖ²` (each
/// `(dₖ, [(j, cₖⱼ)])` with `dₖ > 0` rational and `cₖⱼ` rational), clear all
/// denominators to land entirely in the integer machinery:
///
/// 1. For each square, let `Cₖ = LCM(denominators of cₖⱼ)`; the INTEGER form is
///    `ℓₖ⁺ = Cₖ·ℓₖ` with coefficients `cₖⱼ⁺ = Cₖ·cₖⱼ`. Then
///    `dₖ·ℓₖ² = wₖ·(ℓₖ⁺)²` with `wₖ = dₖ/Cₖ²` (rational, > 0).
/// 2. Let `M = LCM(denominators of all wₖ)`. Then `M·wₖ` is a **nonnegative
///    integer** and `M·p = Σₖ (M·wₖ)·(ℓₖ⁺)²`.
///
/// Returns `Some((M, [(M·wₖ, [(j, cₖⱼ⁺)])]))` — the cleared multiplier `M` and, per
/// square, its integer repetition weight `M·wₖ` and integer-coefficient form — or
/// `None` (decline) on any `i128`/`Rational` overflow, or if `M`, a weight `M·wₖ`, or
/// a form coefficient `|cₖⱼ⁺|` exceeds [`SOS_RATIONAL_MAX`] (keeps the proof bounded).
#[allow(clippy::type_complexity)]
fn clear_rational_sos_denominators(
    squares: &[(Rational, Vec<(usize, Rational)>)],
) -> Option<(i128, Vec<(i128, Vec<(usize, i128)>)>)> {
    // Phase 1: per-square integer form `ℓₖ⁺` and rational weight `wₖ = dₖ/Cₖ²`.
    let mut int_squares: Vec<(Rational, Vec<(usize, i128)>)> = Vec::with_capacity(squares.len());
    for (dk, coeffs) in squares {
        // Cₖ = LCM of the variable-coefficient denominators.
        let mut ck: i128 = 1;
        for &(_, c) in coeffs {
            ck = checked_lcm(ck, c.denominator())?;
            if ck > SOS_RATIONAL_MAX {
                return None;
            }
        }
        // Integer form coefficients cₖⱼ⁺ = Cₖ·cₖⱼ (exact integers by construction).
        let ck_rat = Rational::integer(ck);
        let mut int_coeffs: Vec<(usize, i128)> = Vec::with_capacity(coeffs.len());
        for &(j, c) in coeffs {
            let scaled = c.checked_mul(ck_rat)?;
            if scaled.denominator() != 1 {
                return None; // should be integral after clearing; defensive
            }
            let num = scaled.numerator();
            if num == 0 {
                continue;
            }
            if num.unsigned_abs() > SOS_RATIONAL_MAX as u128 {
                return None;
            }
            int_coeffs.push((j, num));
        }
        if int_coeffs.is_empty() {
            return None; // a zero form refutes nothing
        }
        // wₖ = dₖ / Cₖ² (rational, > 0).
        let ck_sq = ck_rat.checked_mul(ck_rat)?;
        let wk = dk.checked_div(ck_sq)?;
        if wk.is_zero() || wk.numerator() < 0 {
            return None;
        }
        int_squares.push((wk, int_coeffs));
    }
    if int_squares.is_empty() {
        return None;
    }
    // Phase 2: M = LCM of all wₖ denominators.
    let mut m: i128 = 1;
    for (wk, _) in &int_squares {
        m = checked_lcm(m, wk.denominator())?;
        if m > SOS_RATIONAL_MAX {
            return None;
        }
    }
    let m_rat = Rational::integer(m);
    // Per square: integer repetition weight M·wₖ.
    let mut out: Vec<(i128, Vec<(usize, i128)>)> = Vec::with_capacity(int_squares.len());
    for (wk, int_coeffs) in int_squares {
        let mwk = wk.checked_mul(m_rat)?;
        if mwk.denominator() != 1 {
            return None; // M·wₖ must be integral by construction; defensive
        }
        let weight = mwk.numerator();
        if weight <= 0 || weight > SOS_RATIONAL_MAX {
            return None;
        }
        out.push((weight, int_coeffs));
    }
    Some((m, out))
}

/// Reconstruct, **from the SOS certificate**, any strict query `p < 0` whose
/// certificate is a RATIONAL-weight sum of squares `p = Σₖ dₖ·ℓₖ²` (with `dₖ > 0`
/// rational and `ℓₖ` a rational/integer-coefficient linear form, zero affine row) —
/// the slice that unlocks 3-variable AM-GM. Generalizes
/// [`reconstruct_sos_multi_unit_square`] (the integer-weight / ±1-form special case)
/// by **clearing denominators** so everything reduces to the existing integer fold:
/// no scaling lemma is needed.
///
/// Let `M·p = Σₖ (M·wₖ)·(ℓₖ⁺)²` be the cleared identity from
/// [`clear_rational_sos_denominators`] (every `M·wₖ` a nonnegative integer, every
/// `ℓₖ⁺` an integer-coefficient form). Then:
/// - `sosK` = the right-nested `add` of the squares `(ℓₖ⁺·ℓₖ⁺)`, each repeated `M·wₖ`
///   times, last copy as the innermost leaf.
/// - `mpK` = `M` right-nested copies of the asserted `p` (`p + p + … + p`).
/// - `idK : Eq R mpK sosK` via the degree-2 ring normalizer (both sides normalized;
///   canonical gens must agree, else decline — the certificate guarantees it, we
///   re-check it over the kernel, NEVER fabricate the identity).
/// - `nn : le zero sosK` — the existing integer-weight nonnegativity fold over the
///   repeated squares.
/// - `mneg : lt mpK zero` — fold the asserted `hlt : lt p zero` `M` times via
///   `add_lt_add`, casting `add zero zero → zero` on the right at each step so the
///   nesting matches `mpK`.
/// - transport `nn` along `idK` to `lep : le zero mpK`, then `lt_of_le_of_lt zero mpK
///   zero lep mneg : lt zero zero`, refuted by `lt_irrefl zero`.
///
/// Returns `Ok(Some(proof))` (kernel-gated `infer` + `def_eq False`), `Ok(None)` to
/// decline (not this shape, or a bound/overflow/identity-mismatch), or `Err(_)` only
/// on a genuine kernel rejection.
#[allow(clippy::too_many_lines)]
fn reconstruct_sos_rational_weight(
    ctx: &mut LraReconstructCtx,
    arena: &TermArena,
    assertions: &[TermId],
) -> Result<Option<ExprId>, ReconstructError> {
    let Some(cert) = crate::nra_real_root::sos_refute_with_certificate(arena, assertions) else {
        return Ok(None);
    };
    if !cert.strict_lt() {
        return Ok(None);
    }
    let Some(rat_squares) = cert.rational_squares() else {
        return Ok(None);
    };
    let n_vars = cert.n_vars();

    // Clear all denominators: M·p = Σ (M·wₖ)·(ℓₖ⁺)².
    let Some((m, cleared)) = clear_rational_sos_denominators(&rat_squares) else {
        return Ok(None);
    };
    debug_assert!(m >= 1);

    // Faithful encoding of the asserted polynomial p (integer-coefficient).
    let Some(p_rexpr) = cert_poly_to_rexpr(cert.poly_terms(), n_vars) else {
        return Ok(None);
    };

    // Per-square: the integer form ℓₖ⁺ as an RExpr and the square (ℓₖ⁺·ℓₖ⁺), each
    // repeated M·wₖ times (flattened, so the integer-weight fold sees one square per
    // copy — exactly the existing machinery).
    let mut ell_rexprs: Vec<RExpr> = Vec::new();
    let mut sq_rexprs: Vec<RExpr> = Vec::new();
    for (weight, int_coeffs) in &cleared {
        let Some(ell) = int_lin_to_rexpr(int_coeffs) else {
            return Ok(None);
        };
        for _ in 0..*weight {
            sq_rexprs.push(RExpr::Mul(Box::new(ell.clone()), Box::new(ell.clone())));
            ell_rexprs.push(ell.clone());
        }
    }

    // sosK as an RExpr: RIGHT-nested add over all (repeated) squares, last as the
    // innermost leaf (no trailing zero), matching `normalize_deg2`'s faithful form.
    let Some((last, init)) = sq_rexprs.split_last() else {
        return Ok(None);
    };
    let mut sos_rexpr = last.clone();
    for r in init.iter().rev() {
        sos_rexpr = RExpr::Add(Box::new(r.clone()), Box::new(sos_rexpr));
    }

    // mpK as an RExpr: M RIGHT-nested copies of p (p + (p + (… + p))), last as leaf.
    let mut mp_rexpr = p_rexpr.clone();
    for _ in 1..m {
        mp_rexpr = RExpr::Add(Box::new(p_rexpr.clone()), Box::new(mp_rexpr));
    }

    // Normalize M·p and the SOS sum; the canonical gens MUST agree (else decline —
    // re-proving M·p = Σ(M·wₖ)(ℓₖ⁺)² over the kernel, never fabricated).
    let Some((mp_gens, mpk, mp_to_canon)) = ctx.normalize_deg2(&mp_rexpr) else {
        return Ok(None);
    };
    let Some((sos_gens, sosk, sos_to_canon)) = ctx.normalize_deg2(&sos_rexpr) else {
        return Ok(None);
    };
    if mp_gens != sos_gens {
        return Ok(None);
    }

    // idK : Eq R mpK sosK := trans (mpK → canon)(symm (sosK → canon)).
    let canon = ctx.mono_gens_to_expr(&mp_gens);
    let canon_to_sos = ctx.eq_symm_r(sosk, canon, sos_to_canon); // Eq R canon sosK
    let idk = ctx.eq_trans_r(mpk, canon, sosk, mp_to_canon, canon_to_sos); // Eq R mpK sosK

    // Kernel-level per-square ℓₖ⁺ and (ℓₖ⁺·ℓₖ⁺), emitted from the SAME RExprs so the
    // `mul`/`add` ExprIds are hash-consed identical to those inside `sosK`.
    let zero = ctx.mk_zero();
    let mut ells: Vec<ExprId> = Vec::with_capacity(ell_rexprs.len());
    let mut sqs: Vec<ExprId> = Vec::with_capacity(sq_rexprs.len());
    for ell_rexpr in &ell_rexprs {
        let ell = ctx.emit_rexpr(ell_rexpr);
        ells.push(ell);
        sqs.push(ctx.mk_mul(ell, ell));
    }

    // -------------------------------------------------------------------------
    // Nonnegativity fold (existing integer-weight machinery): nn : le zero sosK.
    // sosK = add sq_0 (add sq_1 (… sq_{N-1})). Base = sq_nonneg of the LAST square;
    // fold earlier squares from last-1 down to first, casting `add zero zero → zero`.
    // -------------------------------------------------------------------------
    let nsq = sqs.len();
    let sq_nonneg_of = |ctx: &mut LraReconstructCtx, ell: ExprId| -> ExprId {
        let name = ctx.arith().sq_nonneg;
        let f = ctx.kernel_mut().const_(name, vec![]);
        ctx.kernel_mut().app(f, ell) // le zero (mul ell ell)
    };
    let mut nn = sq_nonneg_of(ctx, ells[nsq - 1]);
    let mut tail = sqs[nsq - 1];
    for idx in (0..nsq - 1).rev() {
        let sq = sqs[idx];
        let sq_k = sq_nonneg_of(ctx, ells[idx]);
        let combined = ctx.add_le_add_app(zero, sq, zero, tail, sq_k, nn);
        let new_tail = ctx.mk_add(sq, tail);
        let lhs = ctx.mk_add(zero, zero);
        let add_zero_zero = ctx.add_zero_eq(zero);
        nn = ctx.le_cast_left(lhs, zero, new_tail, combined, add_zero_zero);
        tail = new_tail;
    }
    debug_assert_eq!(tail, sosk);

    // Transport nn backward along idK (rewrite sosK → mpK) ⇒ lep : le zero mpK.
    let id_sym = ctx.eq_symm_r(mpk, sosk, idk); // Eq R sosK mpK
    let lep = ctx.le_cast_right(zero, sosk, mpk, nn, id_sym);

    // -------------------------------------------------------------------------
    // Negativity M-fold: mneg : lt mpK zero, where
    //   mpK = add p (add p (… p)).  (M right-nested copies, last = leaf)
    // The asserted atom is `hlt : lt p zero`. Seed from the INNERMOST p (the leaf),
    // then fold the earlier copies from M-2 down to 0: combine `hlt : lt p zero` with
    // the running `lt tail zero` via `add_lt_add p zero tail zero hlt acc :
    // lt (add p tail)(add zero zero)`, then cast the RIGHT side
    // `add zero zero → zero` so the type stays `lt (add p tail) zero` — matching
    // `mpK`'s exact right-nesting.
    // -------------------------------------------------------------------------
    // The leaf `p` ExprId used inside mpK (each copy, incl. the innermost, is exactly
    // the faithful encoding of `p_rexpr` — hash-consed identical).
    let p_leaf = ctx.emit_rexpr(&p_rexpr);
    // hlt : lt p zero — the asserted atom `p < 0` over the faithful encoding of p.
    let hlt = {
        let p_prop = ctx.mk_lt(p_leaf, zero);
        ctx.hyp_axiom(p_prop)?
    };
    let mut mneg = hlt; // lt p zero (p_leaf)
    let mut mtail = p_leaf; // running right-nested tail (matches mpK structurally)
    for _ in 1..m {
        // add_lt_add p zero tail zero hlt mneg : lt (add p tail)(add zero zero).
        let combined = ctx.add_lt_add_app(p_leaf, zero, mtail, zero, hlt, mneg);
        let new_tail = ctx.mk_add(p_leaf, mtail); // add p tail (next mpK prefix)
        let add_zz = ctx.mk_add(zero, zero);
        let azz = ctx.add_zero_eq(zero); // Eq R (add zero zero) zero
        mneg = ctx.lt_cast_right(new_tail, add_zz, zero, combined, azz);
        mtail = new_tail;
    }
    debug_assert_eq!(mtail, mpk);

    // chain : lt zero zero := lt_of_le_of_lt zero mpK zero lep mneg.
    let chain = {
        let ax_name = ctx.arith().lt_of_le_of_lt;
        let ax = ctx.kernel_mut().const_(ax_name, vec![]);
        let e = ctx.kernel_mut().app(ax, zero);
        let e = ctx.kernel_mut().app(e, mpk);
        let e = ctx.kernel_mut().app(e, zero);
        let e = ctx.kernel_mut().app(e, lep);
        ctx.kernel_mut().app(e, mneg)
    };
    // bad : False := lt_irrefl zero chain.
    let proof = {
        let irrefl_name = ctx.arith().lt_irrefl;
        let irrefl = ctx.kernel_mut().const_(irrefl_name, vec![]);
        let e = ctx.kernel_mut().app(irrefl, zero);
        ctx.kernel_mut().app(e, chain)
    };

    // Soundness gate.
    let inferred = ctx
        .kernel_mut()
        .infer(proof)
        .map_err(|e| ReconstructError::KernelRejected {
            rule: "sos_rational_weight".to_owned(),
            detail: format!("SOS rational-weight certificate infer failed: {e:?}"),
        })?;
    let false_ = {
        let f = ctx.arith().logic.false_;
        ctx.kernel_mut().const_(f, vec![])
    };
    if ctx.kernel_mut().def_eq(inferred, false_) {
        Ok(Some(proof))
    } else {
        Err(ReconstructError::KernelRejected {
            rule: "sos_rational_weight".to_owned(),
            detail: "SOS rational-weight refutation did not infer to False".to_owned(),
        })
    }
}

/// Reconstruct, **from the SOS certificate**, any STRICT query `p > 0` whose
/// certificate is a rational-weight sum of squares of `−p`. This is the `p > 0`
/// (`strict_lt == false`) dual of [`reconstruct_sos_rational_weight`]: the
/// self-checked certificate certifies `−M ⪰ 0`, so its squares decompose **`−p`**
/// (`−p = Σ dₖ ℓₖ²`, i.e. `p ≤ 0` everywhere), contradicting the asserted `p > 0`.
///
/// Clearing denominators (the SAME [`clear_rational_sos_denominators`] machinery)
/// gives the integer identity `sosK := Σ (M·wₖ)(ℓₖ⁺)² = M·(−p) = −(M·p)`. With
/// `mpK := p + p + … + p` (`M` right-nested copies of `p`):
/// - `nn : le zero sosK` — the SAME integer-weight nonnegativity fold over
///   `sq_nonneg`, `add_le_add`, and the `add zero zero → zero` cast. Only needs
///   `0 ≤ sosK`, which holds regardless of what `sosK` denotes.
/// - `mppos : lt zero mpK` — fold the asserted `hlt : lt zero p` (`0 < p`) `M`
///   times via `add_lt_add` (both premises `lt`, so `0+0 < p+tail`), casting the
///   LEFT `add zero zero → zero` each step so the nesting matches `mpK`.
/// - `combined : lt zero (add sosK mpK)` via `add_lt_add_of_le_of_lt zero sosK zero
///   mpK nn mppos` (summing `0 ≤ sosK` with `0 < mpK`), casting the LEFT `add zero
///   zero → zero`.
/// - `cancel : Eq R (add sosK mpK) zero` — `normalize_deg2(add sosK mpK)` MUST
///   yield EMPTY canonical gens (since `sosK = −(M·p)` and `mpK = M·p` cancel
///   exactly), whose canonical form is the kernel `zero`. If the gens are NOT empty,
///   the certificate/clearing disagree — decline (`Ok(None)`), never fabricate.
/// - `lt_cast_right combined cancel : lt zero zero`, refuted by `lt_irrefl zero`.
///
/// Returns `Ok(Some(proof))` (kernel-gated `infer` + `def_eq False`), `Ok(None)` to
/// decline (not this shape — including `p < 0`, handled by the strict sibling — or a
/// bound/overflow/cancellation mismatch), or `Err(_)` only on a genuine kernel
/// rejection.
#[allow(clippy::too_many_lines)]
fn reconstruct_sos_rational_weight_gt(
    ctx: &mut LraReconstructCtx,
    arena: &TermArena,
    assertions: &[TermId],
) -> Result<Option<ExprId>, ReconstructError> {
    let Some(cert) = crate::nra_real_root::sos_refute_with_certificate(arena, assertions) else {
        return Ok(None);
    };
    // This path owns the `p > 0` (`−M` PSD) dual; the `p < 0` case is the strict
    // sibling's.
    if cert.strict_lt() {
        return Ok(None);
    }
    let Some(rat_squares) = cert.rational_squares() else {
        return Ok(None);
    };
    let n_vars = cert.n_vars();

    // Clear all denominators: `sosK = Σ (M·wₖ)·(ℓₖ⁺)²`. Since the certificate's
    // squares decompose `−p`, this `sosK` equals `M·(−p) = −(M·p)`.
    let Some((m, cleared)) = clear_rational_sos_denominators(&rat_squares) else {
        return Ok(None);
    };
    debug_assert!(m >= 1);

    // Faithful encoding of the asserted polynomial `p` (integer-coefficient).
    let Some(p_rexpr) = cert_poly_to_rexpr(cert.poly_terms(), n_vars) else {
        return Ok(None);
    };

    // Per-square: the integer form `ℓₖ⁺` and the square `(ℓₖ⁺·ℓₖ⁺)`, each repeated
    // `M·wₖ` times (flattened, so the integer-weight fold sees one square per copy).
    let mut ell_rexprs: Vec<RExpr> = Vec::new();
    let mut sq_rexprs: Vec<RExpr> = Vec::new();
    for (weight, int_coeffs) in &cleared {
        let Some(ell) = int_lin_to_rexpr(int_coeffs) else {
            return Ok(None);
        };
        for _ in 0..*weight {
            sq_rexprs.push(RExpr::Mul(Box::new(ell.clone()), Box::new(ell.clone())));
            ell_rexprs.push(ell.clone());
        }
    }

    // `sosK` as an RExpr: RIGHT-nested add over all (repeated) squares, last as the
    // innermost leaf (no trailing zero), matching `normalize_deg2`'s faithful form.
    let Some((last, init)) = sq_rexprs.split_last() else {
        return Ok(None);
    };
    let mut sos_rexpr = last.clone();
    for r in init.iter().rev() {
        sos_rexpr = RExpr::Add(Box::new(r.clone()), Box::new(sos_rexpr));
    }

    // `mpK` as an RExpr: M RIGHT-nested copies of p (p + (p + (… + p))), last = leaf.
    let mut mp_rexpr = p_rexpr.clone();
    for _ in 1..m {
        mp_rexpr = RExpr::Add(Box::new(p_rexpr.clone()), Box::new(mp_rexpr));
    }

    // Kernel-level per-square `ℓₖ⁺` and `(ℓₖ⁺·ℓₖ⁺)`, emitted from the SAME RExprs so
    // the `mul`/`add` ExprIds are hash-consed identical to those inside `sosK`.
    let zero = ctx.mk_zero();
    let mut ells: Vec<ExprId> = Vec::with_capacity(ell_rexprs.len());
    let mut sqs: Vec<ExprId> = Vec::with_capacity(sq_rexprs.len());
    for ell_rexpr in &ell_rexprs {
        let ell = ctx.emit_rexpr(ell_rexpr);
        ells.push(ell);
        sqs.push(ctx.mk_mul(ell, ell));
    }

    // `sosK` as a kernel ExprId: emit from the faithful RExpr (hash-consed identical
    // to the right-nested `add` of `sqs`).
    let sosk = ctx.emit_rexpr(&sos_rexpr);
    // `mpK` as a kernel ExprId: M right-nested copies of `p` (the leaf `p` is the
    // faithful encoding of `p_rexpr`).
    let p_leaf = ctx.emit_rexpr(&p_rexpr);
    let mut mpk = p_leaf;
    for _ in 1..m {
        mpk = ctx.mk_add(p_leaf, mpk);
    }

    // -------------------------------------------------------------------------
    // Nonnegativity fold (existing integer-weight machinery): nn : le zero sosK.
    // sosK = add sq_0 (add sq_1 (… sq_{N-1})). Base = sq_nonneg of the LAST square;
    // fold earlier squares from last-1 down to first, casting `add zero zero → zero`.
    // -------------------------------------------------------------------------
    let nsq = sqs.len();
    let sq_nonneg_of = |ctx: &mut LraReconstructCtx, ell: ExprId| -> ExprId {
        let name = ctx.arith().sq_nonneg;
        let f = ctx.kernel_mut().const_(name, vec![]);
        ctx.kernel_mut().app(f, ell) // le zero (mul ell ell)
    };
    let mut nn = sq_nonneg_of(ctx, ells[nsq - 1]);
    let mut tail = sqs[nsq - 1];
    for idx in (0..nsq - 1).rev() {
        let sq = sqs[idx];
        let sq_k = sq_nonneg_of(ctx, ells[idx]);
        let combined = ctx.add_le_add_app(zero, sq, zero, tail, sq_k, nn);
        let new_tail = ctx.mk_add(sq, tail);
        let lhs = ctx.mk_add(zero, zero);
        let add_zero_zero = ctx.add_zero_eq(zero);
        nn = ctx.le_cast_left(lhs, zero, new_tail, combined, add_zero_zero);
        tail = new_tail;
    }
    debug_assert_eq!(tail, sosk);

    // -------------------------------------------------------------------------
    // Positivity M-fold: mppos : lt zero mpK, where mpK = add p (add p (… p)).
    // The asserted atom is `hlt : lt zero p` (`0 < p`). Seed from the INNERMOST p
    // (the leaf), then fold the earlier copies from M-2 down to 0: combine
    // `hlt : lt zero p` with the running `lt zero tail` via
    // `add_lt_add zero p zero tail hlt acc : lt (add zero zero)(add p tail)`, then
    // cast the LEFT side `add zero zero → zero` so the type stays `lt zero (add p
    // tail)` — matching mpK's exact right-nesting.
    // -------------------------------------------------------------------------
    // hlt : lt zero p — the asserted atom `0 < p` over the faithful encoding of p.
    let hlt = {
        let p_prop = ctx.mk_lt(zero, p_leaf);
        ctx.hyp_axiom(p_prop)?
    };
    let mut mppos = hlt; // lt zero p (p_leaf)
    let mut mtail = p_leaf; // running right-nested tail (matches mpK structurally)
    for _ in 1..m {
        // add_lt_add zero p zero tail hlt mppos : lt (add zero zero)(add p tail).
        let combined = ctx.add_lt_add_app(zero, p_leaf, zero, mtail, hlt, mppos);
        let new_tail = ctx.mk_add(p_leaf, mtail); // add p tail (next mpK prefix)
        let add_zz = ctx.mk_add(zero, zero);
        let azz = ctx.add_zero_eq(zero); // Eq R (add zero zero) zero
        mppos = ctx.lt_cast_left(add_zz, zero, new_tail, combined, azz);
        mtail = new_tail;
    }
    debug_assert_eq!(mtail, mpk);

    // -------------------------------------------------------------------------
    // Combine: add_lt_add_of_le_of_lt zero sosK zero mpK nn mppos
    //   : lt (add zero zero)(add sosK mpK). Cast the LEFT `add zero zero → zero`.
    // -------------------------------------------------------------------------
    let combined_lt = ctx.add_lt_add_of_le_of_lt_app(zero, sosk, zero, mpk, nn, mppos);
    let add_zz = ctx.mk_add(zero, zero);
    let azz = ctx.add_zero_eq(zero); // Eq R (add zero zero) zero
    let sos_plus_mp = ctx.mk_add(sosk, mpk);
    let combined = ctx.lt_cast_left(add_zz, zero, sos_plus_mp, combined_lt, azz);
    // combined : lt zero (add sosK mpK).

    // -------------------------------------------------------------------------
    // Cancellation identity: cancel : Eq R (add sosK mpK) zero. Since sosK = −(M·p)
    // and mpK = M·p, the degree-2 normal form of `add sosK mpK` has EMPTY canonical
    // gens, whose canonical form is the kernel `zero`. The normalizer returns
    // `proof : Eq R (add sosK mpK) (mono_gens_to_expr canon_gens)`; if `canon_gens`
    // is empty, that target IS `zero` (mono_gens_to_expr([]) = mk_zero). If the gens
    // are NOT empty (cancellation failed ⇒ certificate/clearing mismatch), decline —
    // never fabricate the identity.
    // -------------------------------------------------------------------------
    let cancel_rexpr = RExpr::Add(Box::new(sos_rexpr.clone()), Box::new(mp_rexpr.clone()));
    let Some((cancel_gens, cancel_kexpr, cancel_proof)) = ctx.normalize_deg2(&cancel_rexpr) else {
        return Ok(None);
    };
    if !cancel_gens.is_empty() {
        return Ok(None);
    }
    // `cancel_kexpr` is the faithful `add sosK mpK`; assert it matches the combined
    // term so the cast is well-typed (hash-consing makes this an equality of ExprIds).
    if cancel_kexpr != sos_plus_mp {
        return Ok(None);
    }
    // cancel_proof : Eq R (add sosK mpK) zero (canon of empty gens = zero).
    let cancel = cancel_proof;

    // lt_cast_right combined cancel : lt zero zero.
    let lt_zero_zero = ctx.lt_cast_right(zero, sos_plus_mp, zero, combined, cancel);
    // bad : False := lt_irrefl zero (lt zero zero).
    let proof = {
        let irrefl_name = ctx.arith().lt_irrefl;
        let irrefl = ctx.kernel_mut().const_(irrefl_name, vec![]);
        let e = ctx.kernel_mut().app(irrefl, zero);
        ctx.kernel_mut().app(e, lt_zero_zero)
    };

    // Soundness gate.
    let inferred = ctx
        .kernel_mut()
        .infer(proof)
        .map_err(|e| ReconstructError::KernelRejected {
            rule: "sos_rational_weight_gt".to_owned(),
            detail: format!("SOS rational-weight (p>0) certificate infer failed: {e:?}"),
        })?;
    let false_ = {
        let f = ctx.arith().logic.false_;
        ctx.kernel_mut().const_(f, vec![])
    };
    if ctx.kernel_mut().def_eq(inferred, false_) {
        Ok(Some(proof))
    } else {
        Err(ReconstructError::KernelRejected {
            rule: "sos_rational_weight_gt".to_owned(),
            detail: "SOS rational-weight (p>0) refutation did not infer to False".to_owned(),
        })
    }
}

/// Reconstruct the **general** non-strict Farkas refutation. Given the certificate's
/// `≤`-atoms `Eᵢ ≤ 0` (with integer coefficients) and nonnegative rational
/// multipliers `λᵢ`, this:
///
/// 1. clears the multipliers' denominators to integers `μᵢ ≥ 0` (the scaled
///    certificate is an equally-valid refutation);
/// 2. for each used atom declares the hypothesis axiom `hᵢ : le Eᵢ zero`, where `Eᵢ`
///    is the atom's expression in canonical generator form;
/// 3. scales `hᵢ` by `μᵢ` and sums all of them with `add_le_add`, renormalizing the
///    right-hand side back to `zero` at each step, to reach `le Lsum zero`;
/// 4. proves `Eq R Lsum K` with the ring engine (all variable generators cancel,
///    leaving the positive constant `K = Σ μᵢ cᵢ` as a sum of `one`s) and casts to
///    `le K zero`;
/// 5. builds `lt zero K` and closes `lt_of_lt_of_le zero K zero (lt zero K)(le K zero)
///    : lt zero zero`, refuted by `lt_irrefl zero`.
///
/// Returns `Ok(None)` (to fall through to the other shapes) when an atom is strict,
/// has a non-integer coefficient/constant, or the combined constant is not a positive
/// integer — those are outside this engine's non-strict integer scope. The result is
/// kernel-gated (`infer` + `def_eq False`).
#[allow(dead_code, clippy::too_many_lines)]
fn try_general_farkas(
    ctx: &mut LraReconstructCtx,
    certificate: &crate::FarkasCertificate,
) -> Result<Option<ExprId>, ReconstructError> {
    // Used atoms (positive multiplier) with their LinR forms; reject strict /
    // non-integer atoms by falling through.
    let mut used: Vec<(LinR, Rational)> = Vec::new();
    for (atom, m) in certificate.atoms.iter().zip(&certificate.multipliers) {
        if m.is_zero() {
            continue;
        }
        if atom.strict {
            return Ok(None); // mixed/strict combination is not this engine's shape
        }
        let lin = LinR {
            coeffs: atom.coeffs.clone(),
            constant: atom.constant,
        };
        // Integer coefficients/constant only.
        if lin.coeffs.iter().any(|(_, c)| c.denominator() != 1) || lin.constant.denominator() != 1 {
            return Ok(None);
        }
        used.push((lin, *m));
    }
    if used.is_empty() {
        return Ok(None);
    }

    // Clear multiplier denominators: μ = λ · L where L = lcm of denominators. Any
    // `i128` overflow in the denominator-clearing / scaling ⇒ fall through (`None`).
    let mut lcm: i128 = 1;
    for (_, m) in &used {
        let Some(next) = lcm_i128(lcm, m.denominator()) else {
            return Ok(None);
        };
        lcm = next;
    }
    let factor = Rational::integer(lcm);
    let mut scaled: Vec<(LinR, i128)> = Vec::with_capacity(used.len());
    for (lin, m) in &used {
        let Some(mu) = m.checked_mul(factor) else {
            return Ok(None);
        };
        // mu is a nonnegative integer by construction.
        if mu.denominator() != 1 || mu.numerator() <= 0 {
            return Ok(None);
        }
        scaled.push((lin.clone(), mu.numerator()));
    }

    // The combined constant K = Σ μᵢ · constantᵢ (variables provably cancel). The
    // refutation needs K to be a positive integer.
    let mut k_total = Rational::zero();
    let mut combined = LinR::default();
    for (lin, mu) in &scaled {
        let (Some(s), Some(prod)) = (
            scale_lin(lin, Rational::integer(*mu)),
            lin.constant.checked_mul(Rational::integer(*mu)),
        ) else {
            return Ok(None);
        };
        let Some(next) = combined.add(&s) else {
            return Ok(None);
        };
        combined = next;
        let Some(kt) = k_total.checked_add(prod) else {
            return Ok(None);
        };
        k_total = kt;
    }
    if !combined.coeffs.is_empty() {
        // Variables did not cancel — not a genuine Farkas refutation shape.
        return Ok(None);
    }
    if k_total.denominator() != 1 || k_total.numerator() <= 0 {
        return Ok(None);
    }
    let k_int = k_total.numerator();

    // Build the scaled-and-summed `le Lsum zero`, carrying `acc_gens` (the canonical
    // generators of `Lsum`) and `acc_canon_proof : Eq R Lsum (gens_to_expr acc_gens)`.
    let zero = ctx.mk_zero();
    let mut acc: Option<(ExprId, Vec<Gen>, ExprId)> = None; // (le-proof, gens, canon-proof)
    for (lin, mu) in &scaled {
        let Some(base_gens) = LraReconstructCtx::lin_to_gens(lin) else {
            return Ok(None);
        };
        let base_expr = ctx.gens_to_expr(&base_gens);
        // hypothesis hᵢ : le base_expr zero.
        let prop = ctx.mk_le(base_expr, zero);
        let h = ctx.hyp_axiom(prop)?;
        // Scale by μᵢ: combine hᵢ with itself μᵢ times, keeping RHS = zero and the
        // LHS in canonical generator form.
        let mut s_proof = h;
        let mut s_gens = base_gens.clone();
        let mut s_expr = base_expr; // canonical (= gens_to_expr s_gens)
        for _ in 1..*mu {
            // add_le_add s_expr zero base_expr zero s_proof h : le (add s_expr base_expr)(add zero zero)
            let combined_le = ctx.add_le_add_app(s_expr, zero, base_expr, zero, s_proof, h);
            let lhs = ctx.mk_add(s_expr, base_expr);
            // RHS (add zero zero) → zero via add_zero zero.
            let azz = ctx.add_zero_eq(zero); // add zero zero = zero
            let add_zz = ctx.mk_add(zero, zero);
            let combined_le = ctx.le_cast_right(lhs, add_zz, zero, combined_le, azz);
            // LHS (add s_expr base_expr) → canonical (s_gens ++ base_gens).
            let mut next_gens = s_gens.clone();
            next_gens.extend_from_slice(&base_gens);
            let append_proof = ctx.append_eq(&s_gens, &base_gens);
            let next_canon = ctx.gens_to_expr(&next_gens);
            s_proof = ctx.le_cast_left(lhs, next_canon, zero, combined_le, append_proof);
            s_gens = next_gens;
            s_expr = next_canon;
        }
        // Fold this scaled constraint into the accumulator.
        acc = Some(match acc {
            None => (s_proof, s_gens, {
                // canon-proof is refl since s_expr is already canonical.
                ctx.eq_refl_r(s_expr)
            }),
            Some((acc_proof, acc_gens, _acc_canon_proof)) => {
                let acc_expr = ctx.gens_to_expr(&acc_gens);
                // add_le_add acc_expr zero s_expr zero acc_proof s_proof
                let combined_le =
                    ctx.add_le_add_app(acc_expr, zero, s_expr, zero, acc_proof, s_proof);
                let azz = ctx.add_zero_eq(zero);
                let add_zz = ctx.mk_add(zero, zero);
                let lhs = ctx.mk_add(acc_expr, s_expr);
                let combined_le = ctx.le_cast_right(lhs, add_zz, zero, combined_le, azz);
                // LHS (add acc_expr s_expr) → canonical (acc_gens ++ s_gens).
                let mut next_gens = acc_gens.clone();
                next_gens.extend_from_slice(&s_gens);
                let append_proof = ctx.append_eq(&acc_gens, &s_gens);
                let next_canon = ctx.gens_to_expr(&next_gens);
                let new_proof = ctx.le_cast_left(lhs, next_canon, zero, combined_le, append_proof);
                (new_proof, next_gens, ctx.eq_refl_r(next_canon))
            }
        });
    }

    let (le_lsum_zero, all_gens, _canon) = acc.expect("at least one used atom");
    // Normalize all_gens: variables cancel, leaving exactly k_int `One`s.
    let lsum_canon = ctx.gens_to_expr(&all_gens);
    let (norm_gens, norm_proof) = ctx.normalize_gens(&all_gens); // Eq R lsum_canon (gens_to_expr norm_gens)
    // The normalized generators must be exactly `k_int` `One`s (positive constant).
    if norm_gens.len() as i128 != k_int || norm_gens.iter().any(|g| *g != Gen::One) {
        return Ok(None);
    }
    let k_expr = ctx.gens_to_expr(&norm_gens);
    // Cast `le lsum_canon zero` along `lsum_canon = k_expr` ⇒ `le k_expr zero`.
    let le_k_zero = ctx.le_cast_left(lsum_canon, k_expr, zero, le_lsum_zero, norm_proof);
    // lt zero K.
    let lt_zero_k = ctx.lt_zero_ones(k_int);
    // lt_of_lt_of_le zero K zero (lt zero K)(le K zero) : lt zero zero.
    let lt_zero_zero = ctx.lt_of_lt_of_le_app(zero, k_expr, zero, lt_zero_k, le_k_zero);
    // lt_irrefl zero : Not (lt zero zero); apply ⇒ False.
    let proof = {
        let irrefl = ctx.kernel.const_(ctx.arith.lt_irrefl, vec![]);
        let e = ctx.kernel.app(irrefl, zero);
        ctx.kernel.app(e, lt_zero_zero)
    };
    // Soundness gate.
    let inferred = ctx
        .kernel
        .infer(proof)
        .map_err(|e| ReconstructError::KernelRejected {
            rule: "la_generic".to_owned(),
            detail: format!("general-Farkas infer failed: {e:?}"),
        })?;
    let false_ = ctx.kernel.const_(ctx.arith.logic.false_, vec![]);
    if ctx.kernel.def_eq(inferred, false_) {
        Ok(Some(proof))
    } else {
        Err(ReconstructError::KernelRejected {
            rule: "la_generic".to_owned(),
            detail: "general-Farkas refutation did not infer to False".to_owned(),
        })
    }
}

/// Reconstruct a **mixed** strict/non-strict Farkas refutation: the certificate uses
/// at least one strict (`<`) atom with a positive multiplier and is *not* a pure strict
/// cycle (which [`try_strict_cycle`] handles). All used atoms have integer coefficients;
/// multipliers are nonnegative rationals.
///
/// 1. Clear all used multipliers' denominators to integers `μᵢ ≥ 1`.
/// 2. Partition the used atoms by strictness. Sum the non-strict ones (if any) into
///    `le Lne zero` and the strict ones into `lt Lst zero`, each via
///    [`LraReconstructCtx::sum_scaled_atoms`].
/// 3. Combine into one strict inequality `lt Lsum zero`: with both groups present,
///    `add_lt_add_of_le_of_lt (Lne) zero (Lst) zero hle hlt : lt (add Lne Lst)(add zero
///    zero)`, renormalized to `lt (Lne++Lst) zero`; with only strict atoms, `Lsum = Lst`.
/// 4. Normalize `Lsum`'s generators (variables cancel) to the combined constant
///    `K = Σ μᵢ cᵢ`, which must be a **nonnegative** integer (a strict `Σ < 0` with
///    `Σ = K ≥ 0` is the contradiction).
/// 5. Close: `K = 0` gives `lt zero zero` directly (refuted by `lt_irrefl zero`); `K > 0`
///    gives `lt K zero`, and with `lt zero K` (`lt_zero_ones`) `lt_trans zero K zero`
///    yields `lt zero zero`, again refuted by `lt_irrefl zero`.
///
/// Returns `Ok(None)` (fall through) when **no** used atom is strict (the pure non-strict
/// engine owns that), an atom has a non-integer coefficient/constant, variables do not
/// cancel, or `K` is negative. Kernel-gated (`infer` + `def_eq False`).
#[allow(dead_code, clippy::too_many_lines)]
fn try_mixed_farkas(
    ctx: &mut LraReconstructCtx,
    certificate: &crate::FarkasCertificate,
) -> Result<Option<ExprId>, ReconstructError> {
    // Used atoms (positive multiplier) with their LinR + strictness; reject
    // non-integer atoms by falling through.
    let mut used: Vec<(LinR, Rational, bool)> = Vec::new();
    let mut any_strict = false;
    for (atom, m) in certificate.atoms.iter().zip(&certificate.multipliers) {
        if m.is_zero() {
            continue;
        }
        let lin = LinR {
            coeffs: atom.coeffs.clone(),
            constant: atom.constant,
        };
        if lin.coeffs.iter().any(|(_, c)| c.denominator() != 1) || lin.constant.denominator() != 1 {
            return Ok(None);
        }
        any_strict |= atom.strict;
        used.push((lin, *m, atom.strict));
    }
    // This engine only owns the mixed case (≥1 used strict atom). Pure non-strict
    // certificates fall through to `try_general_farkas`.
    if !any_strict || used.is_empty() {
        return Ok(None);
    }

    // Clear all multiplier denominators: μ = λ · L where L = lcm of denominators.
    // Any `i128` overflow in denominator-clearing / scaling ⇒ fall through (`None`).
    let mut lcm: i128 = 1;
    for (_, m, _) in &used {
        let Some(next) = lcm_i128(lcm, m.denominator()) else {
            return Ok(None);
        };
        lcm = next;
    }
    let factor = Rational::integer(lcm);
    let mut strict_atoms: Vec<(LinR, i128)> = Vec::new();
    let mut nonstrict_atoms: Vec<(LinR, i128)> = Vec::new();
    let mut k_total = Rational::zero();
    let mut combined_coeffs = LinR::default();
    for (lin, m, strict) in &used {
        let Some(mu) = m.checked_mul(factor) else {
            return Ok(None);
        };
        if mu.denominator() != 1 || mu.numerator() <= 0 {
            return Ok(None);
        }
        let mu = mu.numerator();
        let (Some(s), Some(prod)) = (
            scale_lin(lin, Rational::integer(mu)),
            lin.constant.checked_mul(Rational::integer(mu)),
        ) else {
            return Ok(None);
        };
        let Some(next) = combined_coeffs.add(&s) else {
            return Ok(None);
        };
        combined_coeffs = next;
        let Some(kt) = k_total.checked_add(prod) else {
            return Ok(None);
        };
        k_total = kt;
        if *strict {
            strict_atoms.push((lin.clone(), mu));
        } else {
            nonstrict_atoms.push((lin.clone(), mu));
        }
    }
    // A genuine refutation cancels all variables, and the strict combined constant must
    // satisfy `K ≥ 0` (the strict sum says `Σ < 0`, refuting `Σ = K ≥ 0`).
    if !combined_coeffs.coeffs.is_empty() {
        return Ok(None);
    }
    if k_total.denominator() != 1 || k_total.numerator() < 0 {
        return Ok(None);
    }
    let k_int = k_total.numerator();
    // `any_strict` ⇒ there is at least one strict atom to sum.
    if strict_atoms.is_empty() {
        return Ok(None);
    }

    let zero = ctx.mk_zero();
    // Strict sub-sum: lt Lst zero (+ its canonical generators).
    let Some((mut lt_proof, mut sum_gens)) = ctx.sum_scaled_atoms(&strict_atoms, true)? else {
        return Ok(None);
    };
    // Fold in the non-strict sub-sum (if any) to keep the result strict.
    if !nonstrict_atoms.is_empty() {
        let Some((le_proof, ne_gens)) = ctx.sum_scaled_atoms(&nonstrict_atoms, false)? else {
            return Ok(None);
        };
        let ne_expr = ctx.gens_to_expr(&ne_gens);
        let st_expr = ctx.gens_to_expr(&sum_gens);
        // add_lt_add_of_le_of_lt ne zero st zero (le ne 0)(lt st 0)
        //   : lt (add ne st)(add zero zero).
        let combined =
            ctx.add_lt_add_of_le_of_lt_app(ne_expr, zero, st_expr, zero, le_proof, lt_proof);
        let azz = ctx.add_zero_eq(zero);
        let add_zz = ctx.mk_add(zero, zero);
        let lhs = ctx.mk_add(ne_expr, st_expr);
        let combined = ctx.lt_cast_right(lhs, add_zz, zero, combined, azz);
        // LHS (add ne st) → canonical (ne_gens ++ st_gens).
        let mut next_gens = ne_gens.clone();
        next_gens.extend_from_slice(&sum_gens);
        let append_proof = ctx.append_eq(&ne_gens, &sum_gens);
        let next_canon = ctx.gens_to_expr(&next_gens);
        lt_proof = ctx.lt_cast_left(lhs, next_canon, zero, combined, append_proof);
        sum_gens = next_gens;
    }

    // Normalize the combined sum: variables cancel, leaving exactly `k_int` `One`s.
    let lsum_canon = ctx.gens_to_expr(&sum_gens);
    let (norm_gens, norm_proof) = ctx.normalize_gens(&sum_gens); // Eq R lsum_canon (gens_to_expr norm_gens)
    if norm_gens.len() as i128 != k_int || norm_gens.iter().any(|g| *g != Gen::One) {
        return Ok(None);
    }
    let k_expr = ctx.gens_to_expr(&norm_gens); // `zero` when k_int == 0.
    // Cast `lt lsum_canon zero` along `lsum_canon = k_expr` ⇒ `lt k_expr zero`.
    let lt_k_zero = ctx.lt_cast_left(lsum_canon, k_expr, zero, lt_proof, norm_proof);
    // Reach `lt zero zero`.
    let lt_zero_zero = if k_int == 0 {
        // k_expr is `zero` (gens_to_expr([]) = zero), so `lt_k_zero : lt zero zero`.
        lt_k_zero
    } else {
        // lt zero K (lt_zero_ones) and lt K zero ⇒ lt_trans zero K zero : lt zero zero.
        let lt_zero_k = ctx.lt_zero_ones(k_int);
        let ax = ctx.kernel.const_(ctx.arith.lt_trans, vec![]);
        let e = ctx.kernel.app(ax, zero);
        let e = ctx.kernel.app(e, k_expr);
        let e = ctx.kernel.app(e, zero);
        let e = ctx.kernel.app(e, lt_zero_k);
        ctx.kernel.app(e, lt_k_zero)
    };
    // lt_irrefl zero : Not (lt zero zero); apply ⇒ False.
    let proof = {
        let irrefl = ctx.kernel.const_(ctx.arith.lt_irrefl, vec![]);
        let e = ctx.kernel.app(irrefl, zero);
        ctx.kernel.app(e, lt_zero_zero)
    };
    // Soundness gate.
    let inferred = ctx
        .kernel
        .infer(proof)
        .map_err(|e| ReconstructError::KernelRejected {
            rule: "la_generic".to_owned(),
            detail: format!("mixed-Farkas infer failed: {e:?}"),
        })?;
    let false_ = ctx.kernel.const_(ctx.arith.logic.false_, vec![]);
    if ctx.kernel.def_eq(inferred, false_) {
        Ok(Some(proof))
    } else {
        Err(ReconstructError::KernelRejected {
            rule: "la_generic".to_owned(),
            detail: "mixed-Farkas refutation did not infer to False".to_owned(),
        })
    }
}

/// `lcm(a, b)` over `i128` (positive inputs; denominators are positive).
/// Declines (`None`) on any `i128` overflow.
fn lcm_i128(a: i128, b: i128) -> Option<i128> {
    if a == 0 || b == 0 {
        return Some(0);
    }
    let g = gcd_i128(a.checked_abs()?, b.checked_abs()?);
    // a / g * b, with g | a exactly.
    (a.checked_abs()? / g).checked_mul(b.checked_abs()?)
}

/// `gcd(a, b)` over nonnegative `i128`.
fn gcd_i128(mut a: i128, mut b: i128) -> i128 {
    while b != 0 {
        let t = b;
        b = a % b;
        a = t;
    }
    a
}

/// Reconstruct a strict-`<` **cycle** refutation: the `n ≥ 2` participating
/// constraints (unit multipliers) form a directed cycle `e0 < e1 < … < e_{n-1} < e0`.
/// Fold `lt_trans` around it to `lt e0 e0`, then `lt_irrefl e0` ⇒ `False`. Generalizes
/// the `n = 2` antisymmetry. Returns `Ok(None)` if the participating constraints are
/// not all strict-`<` or do not form a single cycle; kernel-gated (`infer` + `def_eq
/// False`), so a wrong term is `KernelRejected`, never accepted.
fn try_strict_cycle(
    ctx: &mut LraReconstructCtx,
    arena: &TermArena,
    assertions: &[TermId],
    certificate: &crate::FarkasCertificate,
) -> Result<Option<ExprId>, ReconstructError> {
    let mut participating: Vec<usize> = certificate
        .origins
        .iter()
        .zip(&certificate.multipliers)
        .filter(|(_, m)| !m.is_zero())
        .map(|(&o, _)| o)
        .collect();
    participating.sort_unstable();
    participating.dedup();
    if participating.len() < 2 {
        return Ok(None);
    }
    // Cycles use each constraint once (unit multiplier).
    for (o, m) in certificate.origins.iter().zip(&certificate.multipliers) {
        if participating.contains(o) && !m.is_zero() && *m != Rational::integer(1) {
            return Ok(None);
        }
    }
    // Parse each participating assertion as a strict edge `l < r`.
    let mut edges: Vec<(LinR, LinR)> = Vec::with_capacity(participating.len());
    for &i in &participating {
        match as_lt_constraint(arena, assertions[i]) {
            Some(c) => edges.push(c),
            None => return Ok(None),
        }
    }
    // Order into one cycle: from edge 0, follow `r → next edge whose l == r`.
    let n = edges.len();
    let mut used = vec![false; n];
    let mut order: Vec<usize> = vec![0];
    used[0] = true;
    let mut cur_rhs = edges[0].1.clone();
    for _ in 1..n {
        let Some(j) = (0..n).find(|&j| !used[j] && edges[j].0 == cur_rhs) else {
            return Ok(None);
        };
        used[j] = true;
        order.push(j);
        cur_rhs = edges[j].1.clone();
    }
    // Must close: last RHS == first edge's LHS.
    if cur_rhs != edges[order[0]].0 {
        return Ok(None);
    }
    // Nodes e_k = LHS of the k-th edge in cycle order; edge k is `e_k < e_{(k+1)%n}`.
    let nodes: Vec<ExprId> = order
        .iter()
        .map(|&k| ctx.lin_to_r(&edges[k].0))
        .collect::<Result<_, _>>()?;
    let e0 = nodes[0];
    // h_k : lt e_k e_{(k+1)%n}; fold lt_trans into `acc : lt e0 e_{(k+1)%n}`.
    let mut acc = {
        let p = ctx.mk_lt(nodes[0], nodes[1 % n]);
        ctx.hyp_axiom(p)?
    };
    for k in 1..n {
        let mid = nodes[k];
        let to = nodes[(k + 1) % n];
        let p = ctx.mk_lt(mid, to);
        let hk = ctx.hyp_axiom(p)?;
        let tr = ctx.kernel.const_(ctx.arith.lt_trans, vec![]);
        let e = ctx.kernel.app(tr, e0);
        let e = ctx.kernel.app(e, mid);
        let e = ctx.kernel.app(e, to);
        let e = ctx.kernel.app(e, acc);
        acc = ctx.kernel.app(e, hk);
    }
    // acc : lt e0 e0 ; lt_irrefl e0 acc : False.
    let irrefl = ctx.kernel.const_(ctx.arith.lt_irrefl, vec![]);
    let e = ctx.kernel.app(irrefl, e0);
    let proof = ctx.kernel.app(e, acc);
    let inferred = ctx
        .kernel
        .infer(proof)
        .map_err(|e| ReconstructError::KernelRejected {
            rule: "la_generic".to_owned(),
            detail: format!("infer failed: {e:?}"),
        })?;
    let false_ = ctx.kernel.const_(ctx.arith.logic.false_, vec![]);
    if ctx.kernel.def_eq(inferred, false_) {
        Ok(Some(proof))
    } else {
        Err(ReconstructError::KernelRejected {
            rule: "la_generic".to_owned(),
            detail: "strict-cycle refutation did not infer to False".to_owned(),
        })
    }
}

/// Reconstruct the transitivity-reducible (`e ≤ 0 ∧ 1 ≤ e`) baby-Farkas shape.
///
/// The two participating constraints (those with a positive Farkas multiplier) are
/// re-linearized from the *original* assertion atoms into [`LinR`] form. The shape
/// is accepted only when, for a shared expression `e`, one constraint is `e ≤ 0`
/// and the other is `1 ≤ e` (equivalently `1 - e ≤ 0`), with the multipliers
/// witnessing the same refutation. The reconstruction is the pure order chain.
#[allow(dead_code)]
fn reconstruct_transitivity_refutation(
    ctx: &mut LraReconstructCtx,
    arena: &TermArena,
    assertions: &[TermId],
    certificate: &crate::FarkasCertificate,
) -> Result<ExprId, ReconstructError> {
    // The participating assertion indices: those whose atoms carry a nonzero
    // multiplier. Determinism: origins/multipliers are in atom order.
    let mut participating: Vec<usize> = certificate
        .origins
        .iter()
        .zip(&certificate.multipliers)
        .filter(|(_, m)| !m.is_zero())
        .map(|(&origin, _)| origin)
        .collect();
    participating.sort_unstable();
    participating.dedup();

    let [lo_or_hi_a, lo_or_hi_b] = participating.as_slice() else {
        return Err(ReconstructError::MalformedStep {
            rule: "la_generic".to_owned(),
            detail: format!(
                "slice 1 reconstructs the two-constraint transitivity shape; \
                 {} constraints participate in the certificate",
                participating.len()
            ),
        });
    };

    // Slice 1 reconstructs all-unit (`λ = 1`) multipliers (the baby-Farkas chain
    // does not scale). A non-unit multiplier needs the (deferred) ring normalizer.
    for (origin, m) in certificate.origins.iter().zip(&certificate.multipliers) {
        if (*origin == *lo_or_hi_a || *origin == *lo_or_hi_b)
            && !m.is_zero()
            && *m != Rational::integer(1)
        {
            return Err(ReconstructError::MalformedStep {
                rule: "la_generic".to_owned(),
                detail: format!(
                    "slice 1 reconstructs unit (λ=1) multipliers only; got {}/{} \
                     (the scaling/ring-cancellation normalizer is a later slice)",
                    m.numerator(),
                    m.denominator()
                ),
            });
        }
    }

    // (Strict-`<` antisymmetry is handled upstream by `try_strict_cycle`, the n=2 case.)

    // Re-linearize the two participating assertion atoms into `le L R` shape, as
    // (L − R ≤ 0)-style `LinR`s, but keeping the original two sides so we can match
    // `e ≤ 0` and `1 ≤ e` structurally.
    let (lo_t, hi_t) = (assertions[*lo_or_hi_a], assertions[*lo_or_hi_b]);
    let c0 = as_le_constraint(arena, lo_t).ok_or_else(|| ReconstructError::MalformedStep {
        rule: "la_generic".to_owned(),
        detail: "a participating assertion is not a non-strict `(<= L R)` constraint".to_owned(),
    })?;
    let c1 = as_le_constraint(arena, hi_t).ok_or_else(|| ReconstructError::MalformedStep {
        rule: "la_generic".to_owned(),
        detail: "a participating assertion is not a non-strict `(<= L R)` constraint".to_owned(),
    })?;

    // Identify which is the upper bound `e ≤ 0` and which the lower `1 ≤ e`.
    // c = (left, right) with the relation `left ≤ right`.
    let (e_expr, _matched) =
        match_transitivity_pair(&c0, &c1).ok_or_else(|| ReconstructError::MalformedStep {
            rule: "la_generic".to_owned(),
            detail: "the two constraints are not the transitivity shape `e ≤ 0 ∧ 1 ≤ e`".to_owned(),
        })?;

    // Build the shared `R` expression `e` and the hypothesis Props.
    let e = ctx.lin_to_r(&e_expr)?;
    let zero = ctx.mk_zero();
    let one = ctx.mk_one();

    // h_hi : le e zero  (the upper bound `e ≤ 0`).
    let le_e_zero = ctx.mk_le(e, zero);
    let h_hi = ctx.hyp_axiom(le_e_zero)?;
    // h_lo : le one e   (the lower bound `1 ≤ e`).
    let le_one_e = ctx.mk_le(one, e);
    let h_lo = ctx.hyp_axiom(le_one_e)?;

    // step1 := le_trans one e zero h_lo h_hi : le one zero.
    let step1 = {
        let tr = ctx.kernel.const_(ctx.arith.le_trans, vec![]);
        let e1 = ctx.kernel.app(tr, one);
        let e1 = ctx.kernel.app(e1, e);
        let e1 = ctx.kernel.app(e1, zero);
        let e1 = ctx.kernel.app(e1, h_lo);
        ctx.kernel.app(e1, h_hi)
    };
    // step2 := lt_of_le_of_lt one zero one step1 zero_lt_one : lt one one.
    let step2 = {
        let ax = ctx.kernel.const_(ctx.arith.lt_of_le_of_lt, vec![]);
        let e2 = ctx.kernel.app(ax, one);
        let e2 = ctx.kernel.app(e2, zero);
        let e2 = ctx.kernel.app(e2, one);
        let e2 = ctx.kernel.app(e2, step1);
        let zlo = ctx.kernel.const_(ctx.arith.zero_lt_one, vec![]);
        ctx.kernel.app(e2, zlo)
    };
    // refute := lt_irrefl one step2 : False.
    let proof = {
        let irrefl = ctx.kernel.const_(ctx.arith.lt_irrefl, vec![]);
        let e3 = ctx.kernel.app(irrefl, one); // Not (lt one one)
        ctx.kernel.app(e3, step2) // applied to (lt one one) ⇒ False
    };

    // Soundness gate: infer the term and require it `def_eq` to `False`.
    let inferred = ctx
        .kernel
        .infer(proof)
        .map_err(|e| ReconstructError::KernelRejected {
            rule: "la_generic".to_owned(),
            detail: format!("infer failed: {e:?}"),
        })?;
    let false_ = ctx.kernel.const_(ctx.arith.logic.false_, vec![]);
    if ctx.kernel.def_eq(inferred, false_) {
        Ok(proof)
    } else {
        Err(ReconstructError::KernelRejected {
            rule: "la_generic".to_owned(),
            detail: "inferred proposition is not def-eq to `False`".to_owned(),
        })
    }
}

/// Reconstruct a **Boolean-structured (disjunctive) `QF_LRA`** refutation: a
/// conjunctive linear-real system plus exactly one clause `(L₁ ∨ L₂)` of
/// non-strict literals, each leaf `conj ∧ Lᵢ` conjunctive-Farkas-refutable. The
/// refutation is a kernel case-split (`Or.rec`) on `hor : Enc(L₁ ∨ L₂)`; each
/// branch reuses the conjunctive general-Farkas fold (with the branch literal as
/// the bound hypothesis) to derive `False`, and the eliminator combines them.
///
/// # Errors
///
/// [`ReconstructError::UnsupportedTerm`] when `assertions` is not the disjunctive
/// shape (no single binary clause, a strict / out-of-slice branch literal, or a
/// leaf that is not non-strict-general-Farkas-refutable), or
/// [`ReconstructError::KernelRejected`] if the assembled term fails to kernel-check
/// to `False`. Decision logic is untouched — this only certifies an already-decided
/// `unsat`.
fn reconstruct_disjunctive_lra_proof(
    ctx: &mut LraReconstructCtx,
    arena: &TermArena,
    assertions: &[TermId],
) -> Result<ExprId, ReconstructError> {
    let Some((conj, l1, l2, syms)) = split_disjunctive_lra(arena, assertions) else {
        return Err(ReconstructError::UnsupportedTerm {
            term: "disjunctive-LRA reconstruction needs exactly one binary clause \
                   `(L₁ ∨ L₂)` of non-strict linear-real literals plus conjunctive \
                   real-linear assertions"
                .to_owned(),
        });
    };

    // Encode each branch literal `Enc(Lᵢ) = le Eᵢ zero` (Eᵢ canonical over the
    // shared symbol map), and the clause `Or (Enc L₁) (Enc L₂)` as `hor`.
    let zero = ctx.mk_zero();
    let e1 = ctx.gens_to_expr(&l1.gens);
    let e2 = ctx.gens_to_expr(&l2.gens);
    let enc1 = ctx.mk_le(e1, zero);
    let enc2 = ctx.mk_le(e2, zero);
    let or_prop = {
        let or = ctx.kernel.const_(ctx.arith.logic.or, vec![]);
        let e = ctx.kernel.app(or, enc1);
        ctx.kernel.app(e, enc2)
    };
    let hor = ctx.hyp_axiom(or_prop)?;

    // Build each branch's `False` proof as a function of the bound literal `hᵢ`.
    let minor1 = disjunctive_branch_minor(ctx, arena, &conj, &l1, enc1, &syms)?;
    let minor2 = disjunctive_branch_minor(ctx, arena, &conj, &l2, enc2, &syms)?;

    // motive := fun (_ : Or enc1 enc2) => False.
    let false_ = ctx.kernel.const_(ctx.arith.logic.false_, vec![]);
    let motive = {
        let anon = ctx.kernel.anon();
        ctx.kernel.lam(anon, or_prop, false_, BinderInfo::Default)
    };
    // Or.rec.{0} enc1 enc2 motive minor1 minor2 hor : False.
    let proof = {
        let z = ctx.kernel.level_zero();
        let rec = ctx.kernel.const_(ctx.arith.logic.or_rec, vec![z]);
        let e = ctx.kernel.app(rec, enc1);
        let e = ctx.kernel.app(e, enc2);
        let e = ctx.kernel.app(e, motive);
        let e = ctx.kernel.app(e, minor1);
        let e = ctx.kernel.app(e, minor2);
        ctx.kernel.app(e, hor)
    };

    // Soundness gate: the assembled case-split must kernel-infer to `False`.
    let inferred = ctx
        .kernel
        .infer(proof)
        .map_err(|e| ReconstructError::KernelRejected {
            rule: "disjunctive_la_generic".to_owned(),
            detail: format!("Or.rec case-split infer failed: {e:?}"),
        })?;
    let false_ = ctx.kernel.const_(ctx.arith.logic.false_, vec![]);
    if ctx.kernel.def_eq(inferred, false_) {
        Ok(proof)
    } else {
        Err(ReconstructError::KernelRejected {
            rule: "disjunctive_la_generic".to_owned(),
            detail: "disjunctive-LRA case-split did not infer to False".to_owned(),
        })
    }
}

/// Build the `Or.rec` minor premise `fun (hᵢ : enc_lit) => branchᵢ` for one branch
/// of the disjunctive-LRA case split: bind the branch literal `Lᵢ` as a fresh free
/// variable, reconstruct `branchᵢ : False` over `conj ∧ Lᵢ` (general Farkas, the
/// branch literal supplied as that bound `hᵢ`), then abstract `hᵢ` into the lambda.
fn disjunctive_branch_minor(
    ctx: &mut LraReconstructCtx,
    arena: &TermArena,
    conj: &[TermId],
    lit: &BranchLiteral,
    enc_lit: ExprId,
    syms: &BTreeMap<axeyum_ir::SymbolId, usize>,
) -> Result<ExprId, ReconstructError> {
    let fvar_id = ctx.fresh_fvar_id();
    let h_branch = ctx.kernel.fvar(fvar_id);
    let body = disjunctive_branch_false(ctx, arena, conj, lit, h_branch, syms)?;
    let body = ctx.kernel.abstract_fvars(body, &[fvar_id]);
    let anon = ctx.kernel.anon();
    Ok(ctx.kernel.lam(anon, enc_lit, body, BinderInfo::Default))
}

/// Reconstruct `branchᵢ : False` for the leaf `conj ∧ Lᵢ` via the conjunctive
/// general-Farkas fold, with the branch literal `Lᵢ`'s `le Eᵢ zero` hypothesis
/// supplied as the external proof `h_branch` (the bound `Or.rec` hypothesis) and
/// every conjunctive atom discharged via a fresh `hyp_axiom`. Declines (with an
/// error) when the leaf's certificate is outside the non-strict integer general
/// Farkas slice (a strict used atom, a non-integer coefficient, an overflow, or a
/// non-`±1`-generator branch literal).
fn disjunctive_branch_false(
    ctx: &mut LraReconstructCtx,
    arena: &TermArena,
    conj: &[TermId],
    lit: &BranchLiteral,
    h_branch: ExprId,
    syms: &BTreeMap<axeyum_ir::SymbolId, usize>,
) -> Result<ExprId, ReconstructError> {
    // Re-decide the leaf to obtain self-checked Farkas multipliers (decision logic
    // is unchanged; we only read its certificate). The leaf is `conj ++ [Lᵢ]`.
    let mut leaf: Vec<TermId> = conj.to_vec();
    leaf.push(lit.term);
    let branch_origin = conj.len(); // index of `Lᵢ` in the leaf assertion slice
    let Ok(Some(cert)) = crate::lra_farkas_certificate(arena, &leaf) else {
        return Err(ReconstructError::MalformedStep {
            rule: "disjunctive_la_generic".to_owned(),
            detail: "a disjunctive leaf is not conjunctive-Farkas-refutable".to_owned(),
        });
    };

    // Collect the used (positive-multiplier) atoms, mapping each to global symbol
    // indices and clearing the multiplier denominators to integers `μ ≥ 1`. The
    // branch-literal atom (origin == branch_origin) carries the external `h_branch`
    // proof; every other atom gets a fresh `hyp_axiom`. Strict / non-integer /
    // overflow ⇒ decline (this slice is non-strict integer general Farkas).
    let atoms = collect_branch_farkas_atoms(ctx, &cert, branch_origin, h_branch, &lit.gens, syms)?;
    let Some(atoms) = atoms else {
        return Err(ReconstructError::MalformedStep {
            rule: "disjunctive_la_generic".to_owned(),
            detail: "a disjunctive leaf is outside the non-strict integer general-Farkas slice"
                .to_owned(),
        });
    };
    branch_general_farkas_close(ctx, &atoms)
}

/// One scaled atom of a branch's general-Farkas fold: its canonical base
/// generators `Eⱼ` (the literal denotes `Eⱼ ≤ 0`), the integer multiplier `μⱼ ≥ 1`,
/// and a proof `hⱼ : le (gens_to_expr Eⱼ) zero` (either a fresh `hyp_axiom` for a
/// conjunctive atom, or the bound `Or.rec` hypothesis for the branch literal).
struct BranchAtom {
    gens: Vec<Gen>,
    mu: i128,
    proof: ExprId,
}

/// Translate a leaf's [`FarkasCertificate`] into the [`BranchAtom`] list for the
/// general-Farkas fold, over the **global** symbol indices (so the branch
/// literal's encoding matches the `Or.rec` binding `enc_lit`). Returns `Ok(None)`
/// when the certificate is outside the non-strict integer general-Farkas slice.
fn collect_branch_farkas_atoms(
    ctx: &mut LraReconstructCtx,
    cert: &crate::FarkasCertificate,
    branch_origin: usize,
    h_branch: ExprId,
    branch_gens: &[Gen],
    syms: &BTreeMap<axeyum_ir::SymbolId, usize>,
) -> Result<Option<Vec<BranchAtom>>, ReconstructError> {
    let zero = ctx.mk_zero();
    let mut out: Vec<BranchAtom> = Vec::new();
    for ((atom, m), origin) in cert.atoms.iter().zip(&cert.multipliers).zip(&cert.origins) {
        if m.is_zero() {
            continue;
        }
        if atom.strict {
            return Ok(None); // strict atoms are a later slice
        }
        // Clear the multiplier denominator: μ must be a positive integer.
        if m.denominator() != 1 || m.numerator() <= 0 {
            return Ok(None);
        }
        let mu = m.numerator();
        // Canonical generators of this atom's `E ≤ 0`, over global symbol indices.
        let gens = if *origin == branch_origin {
            branch_gens.to_vec()
        } else {
            let Some(g) = farkas_atom_to_global_gens(atom, &cert.vars, syms) else {
                return Ok(None);
            };
            g
        };
        // The atom's hypothesis proof: the bound `h_branch` for the branch literal,
        // a fresh `hyp_axiom : le base_expr zero` otherwise.
        let proof = if *origin == branch_origin {
            h_branch
        } else {
            let base_expr = ctx.gens_to_expr(&gens);
            let prop = ctx.mk_le(base_expr, zero);
            ctx.hyp_axiom(prop)?
        };
        out.push(BranchAtom { gens, mu, proof });
    }
    if out.is_empty() {
        return Ok(None);
    }
    Ok(Some(out))
}

/// Canonical generators of a [`FarkasAtom`]'s `E ≤ 0` over the **shared** symbol
/// index map `syms`: each coefficient pair `(local_idx, c)` is re-keyed through the
/// certificate's `vars[local_idx]` symbol to the shared index the kernel constants
/// (and the branch literal's encoding) use. Returns `None` on a non-integer
/// coefficient/constant or a symbol missing from the shared map (outside scope).
fn farkas_atom_to_global_gens(
    atom: &crate::FarkasAtom,
    vars: &[axeyum_ir::SymbolId],
    syms: &BTreeMap<axeyum_ir::SymbolId, usize>,
) -> Option<Vec<Gen>> {
    let mut coeffs: Vec<(usize, Rational)> = Vec::with_capacity(atom.coeffs.len());
    for &(local_idx, c) in &atom.coeffs {
        let symbol = *vars.get(local_idx)?;
        let global_idx = *syms.get(&symbol)?;
        coeffs.push((global_idx, c));
    }
    let lin = LinR {
        coeffs,
        constant: atom.constant,
    };
    LraReconstructCtx::lin_to_gens(&lin)
}

/// The fold: combine the [`BranchAtom`]s into `False`. Mirrors the conjunctive
/// `try_general_farkas` engine (scale each atom by `μ` via `add_le_add`, sum to
/// `le Lsum zero`, normalize the generators so variables cancel to a positive
/// constant `K`, and close `K ≤ 0` against `0 < K`), but takes externally-built
/// per-atom proofs (so the branch literal flows in as the bound hypothesis). The
/// conjunctive path is left byte-identical.
fn branch_general_farkas_close(
    ctx: &mut LraReconstructCtx,
    atoms: &[BranchAtom],
) -> Result<ExprId, ReconstructError> {
    let zero = ctx.mk_zero();
    let mut acc: Option<(ExprId, Vec<Gen>)> = None; // (le-proof, gens)
    for atom in atoms {
        let base_gens = &atom.gens;
        let base_expr = ctx.gens_to_expr(base_gens);
        // Scale by μ: combine the atom's proof with itself μ times (RHS stays zero,
        // LHS kept in canonical generator form).
        let mut s_proof = atom.proof;
        let mut s_gens = base_gens.clone();
        let mut s_expr = base_expr;
        for _ in 1..atom.mu {
            let combined = ctx.add_le_add_app(s_expr, zero, base_expr, zero, s_proof, atom.proof);
            let lhs = ctx.mk_add(s_expr, base_expr);
            let azz = ctx.add_zero_eq(zero);
            let add_zz = ctx.mk_add(zero, zero);
            let combined = ctx.le_cast_right(lhs, add_zz, zero, combined, azz);
            let mut next_gens = s_gens.clone();
            next_gens.extend_from_slice(base_gens);
            let append_proof = ctx.append_eq(&s_gens, base_gens);
            let next_canon = ctx.gens_to_expr(&next_gens);
            s_proof = ctx.le_cast_left(lhs, next_canon, zero, combined, append_proof);
            s_gens = next_gens;
            s_expr = next_canon;
        }
        acc = Some(match acc {
            None => (s_proof, s_gens),
            Some((acc_proof, acc_gens)) => {
                let acc_expr = ctx.gens_to_expr(&acc_gens);
                let combined = ctx.add_le_add_app(acc_expr, zero, s_expr, zero, acc_proof, s_proof);
                let azz = ctx.add_zero_eq(zero);
                let add_zz = ctx.mk_add(zero, zero);
                let lhs = ctx.mk_add(acc_expr, s_expr);
                let combined = ctx.le_cast_right(lhs, add_zz, zero, combined, azz);
                let mut next_gens = acc_gens.clone();
                next_gens.extend_from_slice(&s_gens);
                let append_proof = ctx.append_eq(&acc_gens, &s_gens);
                let next_canon = ctx.gens_to_expr(&next_gens);
                let new_proof = ctx.le_cast_left(lhs, next_canon, zero, combined, append_proof);
                (new_proof, next_gens)
            }
        });
    }
    let (le_lsum_zero, all_gens) = acc.expect("at least one branch atom");
    // Normalize: variables cancel, leaving exactly `K` `One`s with `K > 0`.
    let lsum_canon = ctx.gens_to_expr(&all_gens);
    let (norm_gens, norm_proof) = ctx.normalize_gens(&all_gens);
    let k_int = i128::try_from(norm_gens.len()).map_err(|_| ReconstructError::MalformedStep {
        rule: "disjunctive_la_generic".to_owned(),
        detail: "normalized constant overflows i128".to_owned(),
    })?;
    if k_int <= 0 || norm_gens.iter().any(|g| *g != Gen::One) {
        return Err(ReconstructError::MalformedStep {
            rule: "disjunctive_la_generic".to_owned(),
            detail: "branch Farkas combination did not reduce to a positive constant".to_owned(),
        });
    }
    let k_expr = ctx.gens_to_expr(&norm_gens);
    let le_k_zero = ctx.le_cast_left(lsum_canon, k_expr, zero, le_lsum_zero, norm_proof);
    let lt_zero_k = ctx.lt_zero_ones(k_int);
    let lt_zero_zero = ctx.lt_of_lt_of_le_app(zero, k_expr, zero, lt_zero_k, le_k_zero);
    let irrefl = ctx.kernel.const_(ctx.arith.lt_irrefl, vec![]);
    let e = ctx.kernel.app(irrefl, zero);
    Ok(ctx.kernel.app(e, lt_zero_zero))
}

// ===========================================================================
// Boolean-structured (disjunctive) QF_LRA reconstruction.
//
// The conjunctive Farkas path (`reconstruct_lra_proof`) handles only assertion
// sets that the conjunctive decision procedure can collect — a top-level
// positive `Or` is reported `Unsupported` by `lra_farkas_certificate`, so a
// disjunctive UNSAT carries NO Lean proof there. This block closes the smallest
// uncovered disjunctive shape: a conjunctive linear-real system plus exactly one
// clause `(L₁ ∨ L₂)` of NON-STRICT linear-real literals, where each leaf
// `conj ∧ Lᵢ` is conjunctive-Farkas-refutable.
//
// The reconstruction is a kernel case-split (`Or.rec`, the eliminator behind
// `Or.elim`) on a hypothesis `hor : Enc(L₁ ∨ L₂)`. Each minor premise binds the
// branch literal `hᵢ : Enc(Lᵢ)` as a free variable, reuses the conjunctive
// general-Farkas fold to derive `branchᵢ : False` (the conjunctive atoms remain
// the verbatim `hyp_axiom` hypotheses; only the branch literal flows in as the
// bound `hᵢ`), then abstracts `hᵢ` into a `fun (hᵢ : Enc Lᵢ) => branchᵢ` lambda.
// The kernel `infer`s the assembled `Or.rec … hor : False`; a wrong fold ⇒
// `KernelRejected`, never a wrong `False`. The only added axioms are the
// conjunctive constraint hypotheses and `hor` (the verbatim disjunction).
// ===========================================================================

/// A non-strict real linear literal `Lᵢ` already normalized to `E ≤ 0` form, as
/// the canonical generators of `E` (over a *shared* symbol→index map) plus the
/// originating IR [`TermId`]. Built by [`disjunctive_branch_literal`].
#[derive(Debug, Clone)]
struct BranchLiteral {
    /// Canonical generators of `E` where the literal denotes `E ≤ 0`.
    gens: Vec<Gen>,
    /// The original IR atom (a real `≤`/`≥`), used to drive the per-leaf
    /// conjunctive decision procedure.
    term: TermId,
}

/// Normalize a non-strict real literal `term` (`l ≤ r` / `l ≥ r`) to `E ≤ 0` and
/// return its canonical generators over the **shared** symbol→index map `syms`
/// (so two literals / the conjunctive atoms agree on every variable's kernel
/// constant). `E = l − r` for `≤`, `E = r − l` for `≥`. Returns `None` for a
/// strict / non-real / out-of-slice literal (any coefficient outside the
/// generator alphabet ±1·var, ±1).
fn disjunctive_branch_literal(
    arena: &TermArena,
    term: TermId,
    syms: &mut BTreeMap<axeyum_ir::SymbolId, usize>,
) -> Option<BranchLiteral> {
    let IrTermNode::App { op, args } = arena.node(term) else {
        return None;
    };
    if args.len() != 2 {
        return None;
    }
    let l = real_to_lin_inner(arena, args[0], syms)?;
    let r = real_to_lin_inner(arena, args[1], syms)?;
    // `l ≤ r` ⇒ `l − r ≤ 0`; `l ≥ r` ⇒ `r − l ≤ 0`. Strict / non-comparison: decline.
    let e = match op {
        IrOp::RealLe => l.sub(&r)?,
        IrOp::RealGe => r.sub(&l)?,
        _ => return None,
    };
    let gens = LraReconstructCtx::lin_to_gens(&e)?;
    Some(BranchLiteral { gens, term })
}

/// The structural decomposition of a disjunctive-LRA query (the output of
/// [`split_disjunctive_lra`]): the conjunctive assertion [`TermId`]s, the two
/// parsed branch literals of the single clause, and the shared symbol→index map
/// over which every literal's and conjunctive atom's variables are encoded.
type DisjunctiveSplit = (
    Vec<TermId>,
    BranchLiteral,
    BranchLiteral,
    BTreeMap<axeyum_ir::SymbolId, usize>,
);

/// Split `assertions` into `(conj, l1, l2, syms)` for the disjunctive-LRA shape:
/// **exactly one** assertion is a binary `Or` of two non-strict real-linear
/// literals, and every other assertion is a conjunctive real-linear constraint
/// (`≤`/`<`/`=`/`≥`/`>`). Returns the conjunctive [`TermId`]s and the two parsed
/// branch literals (over a shared symbol→index map). `None` if the shape does not
/// hold (no clause, more than one clause, a strict / out-of-slice branch literal,
/// or a non-linear conjunctive assertion).
fn split_disjunctive_lra(arena: &TermArena, assertions: &[TermId]) -> Option<DisjunctiveSplit> {
    let mut syms: BTreeMap<axeyum_ir::SymbolId, usize> = BTreeMap::new();
    let mut conj: Vec<TermId> = Vec::new();
    let mut clause: Option<(BranchLiteral, BranchLiteral)> = None;
    for &a in assertions {
        if let IrTermNode::App {
            op: IrOp::BoolOr,
            args,
        } = arena.node(a)
        {
            if args.len() != 2 || clause.is_some() {
                return None; // not binary, or a second clause — out of this slice
            }
            let l1 = disjunctive_branch_literal(arena, args[0], &mut syms)?;
            let l2 = disjunctive_branch_literal(arena, args[1], &mut syms)?;
            clause = Some((l1, l2));
        } else {
            // A conjunctive assertion: it must be a real-linear constraint so the
            // shared symbol map covers its variables (and the leaf decides cleanly).
            if as_le_constraint(arena, a).is_none()
                && as_lt_constraint(arena, a).is_none()
                && !is_real_eq_constraint(arena, a, &mut syms)
            {
                return None;
            }
            // Thread the conjunctive variables through the shared map too.
            register_real_vars(arena, a, &mut syms);
            conj.push(a);
        }
    }
    let (l1, l2) = clause?;
    Some((conj, l1, l2, syms))
}

/// Whether `term` is a real equality `a = b` over the linear subset, threading its
/// variables into the shared `syms` map.
fn is_real_eq_constraint(
    arena: &TermArena,
    term: TermId,
    syms: &mut BTreeMap<axeyum_ir::SymbolId, usize>,
) -> bool {
    let IrTermNode::App { op: IrOp::Eq, args } = arena.node(term) else {
        return false;
    };
    if args.len() != 2 || arena.sort_of(args[0]) != IrSort::Real {
        return false;
    }
    real_to_lin_inner(arena, args[0], syms).is_some()
        && real_to_lin_inner(arena, args[1], syms).is_some()
}

/// Register every real variable reachable in `term` into the shared symbol→index
/// map (in first-seen order), so the kernel constant for a symbol is the same
/// whether it appears in a conjunctive atom or a branch literal.
fn register_real_vars(
    arena: &TermArena,
    term: TermId,
    syms: &mut BTreeMap<axeyum_ir::SymbolId, usize>,
) {
    let mut stack = vec![term];
    let mut seen = BTreeSet::new();
    while let Some(t) = stack.pop() {
        if !seen.insert(t) {
            continue;
        }
        if let IrTermNode::Symbol(s) = arena.node(t) {
            if arena.sort_of(t) == IrSort::Real {
                let next = syms.len();
                syms.entry(*s).or_insert(next);
            }
        }
        if let IrTermNode::App { args, .. } = arena.node(t) {
            stack.extend(args.iter().copied());
        }
    }
}

/// Detect the **disjunctive-LRA refutation** shape: the [`split_disjunctive_lra`]
/// structure holds **and** each leaf `conj ∧ Lᵢ` is conjunctive-Farkas-refutable
/// (`unsat`). A satisfiable disjunctive set (some leaf is `sat`) returns `false`
/// so no fabricated proof is routed. The whole set being UNSAT follows from both
/// leaves being UNSAT (`(L₁ ∨ L₂) ∧ conj` is unsat iff `conj ∧ L₁` and
/// `conj ∧ L₂` are both unsat).
#[must_use]
fn is_disjunctive_lra_refutation(arena: &TermArena, assertions: &[TermId]) -> bool {
    let Some((conj, l1, l2, _syms)) = split_disjunctive_lra(arena, assertions) else {
        return false;
    };
    leaf_is_farkas_unsat(arena, &conj, l1.term) && leaf_is_farkas_unsat(arena, &conj, l2.term)
}

/// Whether the leaf `conj ∧ literal` has a (self-checked) conjunctive Farkas
/// refutation. Any decision error / `sat` / `unknown` ⇒ `false` (decline).
fn leaf_is_farkas_unsat(arena: &TermArena, conj: &[TermId], literal: TermId) -> bool {
    let mut leaf: Vec<TermId> = conj.to_vec();
    leaf.push(literal);
    matches!(crate::lra_farkas_certificate(arena, &leaf), Ok(Some(_)))
}

/// A non-strict `(<= left right)` constraint as `(left_lin, right_lin)` linear
/// forms, or `None` if `term` is not a real `≤`/`≥` over the linear subset this
/// slice handles. A `≥` is normalized by swapping sides into `≤` form.
#[allow(dead_code)]
fn as_le_constraint(arena: &TermArena, term: TermId) -> Option<(LinR, LinR)> {
    let IrTermNode::App { op, args } = arena.node(term) else {
        return None;
    };
    if args.len() != 2 {
        return None;
    }
    let (l, r) = (real_to_lin(arena, args[0])?, real_to_lin(arena, args[1])?);
    match op {
        IrOp::RealLe => Some((l, r)),
        IrOp::RealGe => Some((r, l)),
        _ => None,
    }
}

/// Parse a strict real comparison `(< L R)` / `(> L R)` into `(L, R)` with the
/// relation `L < R` (`>` swapped), each side a [`LinR`]. Returns `None` for a
/// non-strict or non-real-comparison term.
fn as_lt_constraint(arena: &TermArena, term: TermId) -> Option<(LinR, LinR)> {
    let IrTermNode::App { op, args } = arena.node(term) else {
        return None;
    };
    if args.len() != 2 {
        return None;
    }
    let (l, r) = (real_to_lin(arena, args[0])?, real_to_lin(arena, args[1])?);
    match op {
        IrOp::RealLt => Some((l, r)),
        IrOp::RealGt => Some((r, l)),
        _ => None,
    }
}

/// Lower an IR real term to a [`LinR`] over dense variable indices keyed by symbol,
/// for the linear subset (`Symbol`, `RealConst`, `RealNeg`, `RealAdd`, `RealSub`,
/// and `RealMul` with a constant factor). Returns `None` outside that fragment.
#[allow(dead_code)]
fn real_to_lin(arena: &TermArena, term: TermId) -> Option<LinR> {
    real_to_lin_inner(arena, term, &mut BTreeMap::new())
}

/// As [`real_to_lin`], threading the (symbol → dense index) memo so repeated
/// variables share an index, in first-seen order.
#[allow(dead_code)]
fn real_to_lin_inner(
    arena: &TermArena,
    term: TermId,
    vars: &mut BTreeMap<axeyum_ir::SymbolId, usize>,
) -> Option<LinR> {
    match arena.node(term) {
        IrTermNode::RealConst(value) => Some(LinR::constant(*value)),
        IrTermNode::Symbol(symbol) if arena.sort_of(term) == IrSort::Real => {
            let next = vars.len();
            let index = *vars.entry(*symbol).or_insert(next);
            Some(LinR::var(index))
        }
        IrTermNode::App {
            op: IrOp::RealNeg,
            args,
        } => real_to_lin_inner(arena, args[0], vars)?.neg(),
        IrTermNode::App {
            op: IrOp::RealAdd,
            args,
        } => {
            let a = real_to_lin_inner(arena, args[0], vars)?;
            let b = real_to_lin_inner(arena, args[1], vars)?;
            a.add(&b)
        }
        IrTermNode::App {
            op: IrOp::RealSub,
            args,
        } => {
            let a = real_to_lin_inner(arena, args[0], vars)?;
            let b = real_to_lin_inner(arena, args[1], vars)?;
            a.sub(&b)
        }
        IrTermNode::App {
            op: IrOp::RealMul,
            args,
        } => {
            let a = real_to_lin_inner(arena, args[0], vars)?;
            let b = real_to_lin_inner(arena, args[1], vars)?;
            // Linear: one factor must be a bare constant.
            if a.coeffs.is_empty() {
                scale_lin(&b, a.constant)
            } else if b.coeffs.is_empty() {
                scale_lin(&a, b.constant)
            } else {
                None
            }
        }
        _ => None,
    }
}

/// Scale a [`LinR`] by a constant factor, declining (`None`) on any `i128`
/// overflow (the caller then falls back to a non-reconstruction path / decline).
#[allow(dead_code)]
fn scale_lin(lin: &LinR, factor: Rational) -> Option<LinR> {
    if factor.is_zero() {
        return Some(LinR::constant(Rational::zero()));
    }
    let mut coeffs = Vec::with_capacity(lin.coeffs.len());
    for &(i, c) in &lin.coeffs {
        coeffs.push((i, c.checked_mul(factor)?));
    }
    Some(LinR {
        coeffs,
        constant: lin.constant.checked_mul(factor)?,
    })
}

/// Match two `≤`-constraints `(l0 ≤ r0)`, `(l1 ≤ r1)` as the transitivity shape
/// `e ≤ 0 ∧ 1 ≤ e` for a shared bare-variable expression `e`. Returns `(e, ())`
/// (the shared expression as a [`LinR`]) when matched, else `None`.
///
/// Slice 1 fixes `e` to a single bare variable so the order chain stays the literal
/// baby-Farkas shape (`le one e`, `le e zero`); the general affine `e` and scaled
/// multipliers are a later slice.
#[allow(dead_code)]
fn match_transitivity_pair(c0: &(LinR, LinR), c1: &(LinR, LinR)) -> Option<(LinR, ())> {
    // Normalize each constraint `l ≤ r` to `(e, role)` where role is upper bound
    // `e ≤ 0` (r is 0, l is the bare var) or lower bound `1 ≤ e` (l is 1, r is the
    // bare var).
    let classify = |c: &(LinR, LinR)| -> Option<(usize, Bound)> {
        let (l, r) = c;
        if let Some(v) = l.as_bare_var() {
            if r.is_constant_eq(Rational::zero()) {
                return Some((v, Bound::Upper)); // v ≤ 0
            }
        }
        if let Some(v) = r.as_bare_var() {
            if l.is_constant_eq(Rational::integer(1)) {
                return Some((v, Bound::Lower)); // 1 ≤ v
            }
        }
        None
    };
    let (v0, b0) = classify(c0)?;
    let (v1, b1) = classify(c1)?;
    if v0 != v1 || b0 == b1 {
        return None; // must be the SAME variable, one upper and one lower bound
    }
    Some((LinR::var(v0), ()))
}

/// Which bound a transitivity constraint plays in `e ≤ 0 ∧ 1 ≤ e`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[allow(dead_code)]
enum Bound {
    /// `e ≤ 0` (an upper bound on `e`).
    Upper,
    /// `1 ≤ e` (a lower bound on `e`).
    Lower,
}

#[cfg(test)]
mod tests;
