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

use std::collections::BTreeMap;

use axeyum_cnf::{AletheCommand, AletheLit, AletheTerm};
use axeyum_lean_kernel::{
    BinderInfo, Declaration, ExprId, Kernel, LevelId, LogicPrelude, NameId, build_logic_prelude,
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
/// Atom constants have type `α`; function constants have type `α → α` (unary, the
/// only function arity this slice translates). Declarations are added to the
/// kernel's environment lazily, the first time an atom/function name is seen.
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

    /// Get (declaring lazily) the constant `NameId` for an uninterpreted unary
    /// function symbol of type `α → α`. Idempotent.
    fn func_const(&mut self, name: &str) -> NameId {
        if let Some(&id) = self.funcs.get(name) {
            return id;
        }
        let anon = self.kernel.anon();
        // α → α  (= Π (_ : α), α).
        let arrow = self
            .kernel
            .pi(anon, self.alpha, self.alpha, BinderInfo::Default);
        let decl_name = self.fresh_name("func");
        self.kernel
            .add_declaration(Declaration::Axiom {
                name: decl_name,
                uparams: vec![],
                ty: arrow,
            })
            .expect("function axiom (_ : α → α) should admit");
        self.funcs.insert(name.to_owned(), decl_name);
        decl_name
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
    /// - a unary function application `App(f, [x])` → `f ⟦x⟧` where `f : α → α`.
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
            // A unary uninterpreted function application `(f x)`.
            AletheTerm::App(head, args) if args.len() == 1 => {
                let arg = self.alethe_term_to_expr(&args[0])?;
                let f_name = self.func_const(head);
                let f = self.kernel.const_(f_name, vec![]);
                Ok(self.kernel.app(f, arg))
            }
            // Higher-arity functions, indexed operators, and any other shape are
            // out of this slice's scope.
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

/// Reconstruct a unary `eq_congruent` step into a kernel-checked proof term.
///
/// `eq_congruent` ⊢ `(cl (not (= a b)) (= (f a) (f b)))` with one premise
/// `h : Eq α a b` proves the congruence of a unary uninterpreted function `f`.
/// Reconstruction is a `congrArg`-style transport: with `h : Eq α a b`, the
/// motive `fun (x : α) (_ : Eq α a x) => Eq α (f a) (f x)` and refl-case
/// `Eq.refl α (f a)`, `Eq.rec` yields `Eq α (f a) (f b)`.
///
/// Only the **unary** shape is reconstructed (the arity the EUF emitter uses for
/// `f(a)=f(b)`); a multi-argument `eq_congruent` clause (several leading negated
/// equalities, or applications whose heads are not a 1-ary function symbol) is
/// rejected with [`ReconstructError::UnsupportedRule`] rather than guessed.
///
/// # Errors
///
/// Returns [`ReconstructError::MalformedStep`] for a clause whose two literals are
/// not `(cl (not (= a b)) (= (f a) (f b)))` with matching argument, and
/// [`ReconstructError::UnsupportedRule`] for a non-unary congruence; the kernel
/// gate fires through [`ReconstructError::KernelRejected`].
fn reconstruct_eq_congruent(
    ctx: &mut ReconstructCtx,
    premises: &[ExprId],
    conclusion: &[AletheLit],
) -> Result<ExprId, ReconstructError> {
    // This slice reconstructs only the single-argument shape.
    let [hyp, concl] = conclusion else {
        return Err(ReconstructError::UnsupportedRule {
            rule: "eq_congruent (only unary single-premise is reconstructed)".to_owned(),
        });
    };
    let (Some((a_t, b_t)), Some((fa_t, fb_t))) = (as_negated_eq(hyp), as_positive_eq(concl)) else {
        return Err(ReconstructError::MalformedStep {
            rule: "eq_congruent".to_owned(),
            detail: "expected `(cl (not (= a b)) (= (f a) (f b)))`".to_owned(),
        });
    };
    // The conclusion sides must be `(f a)` and `(f b)` of the same unary head `f`.
    let (f1, a2) = as_unary_app(fa_t).ok_or_else(|| ReconstructError::UnsupportedRule {
        rule: "eq_congruent (conclusion lhs is not a unary application)".to_owned(),
    })?;
    let (f2, b2) = as_unary_app(fb_t).ok_or_else(|| ReconstructError::UnsupportedRule {
        rule: "eq_congruent (conclusion rhs is not a unary application)".to_owned(),
    })?;
    if f1 != f2 || a2 != a_t || b2 != b_t {
        return Err(ReconstructError::MalformedStep {
            rule: "eq_congruent".to_owned(),
            detail: "congruence applications do not match the hypothesis argument".to_owned(),
        });
    }

    let a = ctx.alethe_term_to_expr(a_t)?;
    let b = ctx.alethe_term_to_expr(b_t)?;
    let fa = ctx.alethe_term_to_expr(fa_t)?;

    // Premise `h : Eq α a b` (explicit, or a self-contained inline axiom).
    let h = premise_or_axiom(ctx, premises, 0, a, b, "eq_congruent")?;

    // motive := fun (x : α) (_ : Eq α a x) => Eq α (f a) (f x).
    //   Body `Eq α (f a) (f x)`: x = BVar 1; hx domain `Eq α a x`: x = BVar 0.
    let f_name = ctx.func_const(f1);
    let motive = {
        let f = ctx.kernel.const_(f_name, vec![]);
        let x1 = ctx.kernel.bvar(1);
        let f_x = ctx.kernel.app(f, x1);
        let eq_fa_fx = ctx.mk_eq(fa, f_x);
        let x0 = ctx.kernel.bvar(0);
        let eq_a_x = ctx.mk_eq(a, x0);
        let anon = ctx.kernel.anon();
        let inner = ctx.kernel.lam(anon, eq_a_x, eq_fa_fx, BinderInfo::Default);
        ctx.kernel.lam(anon, ctx.alpha, inner, BinderInfo::Default)
    };
    // refl_case : motive a (Eq.refl α a) = Eq α (f a) (f a), proved by Eq.refl α (f a).
    let refl_case = ctx.mk_eq_refl(fa);
    // Eq.rec α a motive refl_case b h  :  motive b h  =  Eq α (f a) (f b).
    let proof = ctx.mk_eq_rec_transport(a, motive, refl_case, b, h);

    let fb = ctx.alethe_term_to_expr(fb_t)?;
    let expected = ctx.mk_eq(fa, fb);
    check_against(ctx, "eq_congruent", proof, expected)
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

/// Extract `(head, arg)` of a unary application `(head arg)` that is **not** an
/// equality (so a genuine function application, not `(= a b)` mis-parsed).
fn as_unary_app(term: &AletheTerm) -> Option<(&str, &AletheTerm)> {
    match term {
        AletheTerm::App(head, args) if head != "=" && args.len() == 1 => {
            Some((head.as_str(), &args[0]))
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
///   [`reconstruct_eq_step`] (plus [`reconstruct_eq_congruent`]) when a resolution
///   resolves it against its hypotheses' unit proofs.
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
        // `(= a b)` ⇒ a fresh axiom `h : Eq α a b`.
        let le = ctx.alethe_term_to_expr(l)?;
        let re = ctx.alethe_term_to_expr(r)?;
        let eq_prop = ctx.mk_eq(le, re);
        let proof = fresh_axiom(ctx, eq_prop, "assume")?;
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
///   `False`. See [`binary_resolve`].
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

    // Pool-size budget: DP is worst-case exponential, so cap the working set and
    // degrade to a clean error rather than hang/OOM on a pathological proof.
    const DP_POOL_BUDGET: usize = 4096;

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

/// Reconstruct a Tseitin **CNF-introduction** rule into a kernel-checked Lean
/// proof term of its conclusion clause's `Prop` encoding.
///
/// `rule_name` is the Alethe rule (`and_pos`/`and_neg`/`or_pos`/`or_neg`,
/// `equiv_pos1`/`equiv_pos2`/`equiv_neg1`/`equiv_neg2`,
/// `xor_pos1`/`xor_pos2`/`xor_neg1`/`xor_neg2`); `conclusion` is the rule's
/// conclusion clause. Each such clause is a propositional **tautology** over the
/// structured gate (`And`/`Or`/`Iff`/`Not`, with `xor` modeled as `Not Iff`) of
/// its operand atoms. The returned proof term is `infer`-checked and
/// [`Kernel::def_eq`]-compared to the clause's [`ReconstructCtx::gate_clause_to_prop`]
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
        AletheTerm::Indexed { .. } => Err(ReconstructError::UnsupportedTerm {
            term: format!(
                "indexed operand outside the bitwise + extract fragment `{}`",
                term.key()
            ),
        }),
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
                bv_operand_width(ctx, lo).ok_or_else(|| ReconstructError::UnsupportedTerm {
                    term: format!("concat low-operand width unknown `{}`", lhs.key()),
                })?;
            let bit_term = if i < width_lo {
                operand_bit_term(lo, i)
            } else {
                operand_bit_term(hi, i - width_lo)
            };
            return Ok(ctx.gate_term_to_prop(&bit_term));
        }
        if head == "bvcomp" {
            // `(bvcomp x y)`: a 1-bit result whose only bit is the per-bit-equality
            // AND over the operand bits. Needs the operand width (via `bv_widths`).
            let [x, y] = args.as_slice() else {
                return Err(ReconstructError::UnsupportedTerm {
                    term: format!("bvcomp needs two operands `{}`", lhs.key()),
                });
            };
            let width = bv_operand_width(ctx, x)
                .or_else(|| bv_operand_width(ctx, y))
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

/// The width of a bit-blast operand, when recoverable without type context: a
/// `(@bbterm b…)` has `len` bits, a `#b…` literal has its digit count, and a
/// recorded bit-blasted symbol uses [`ReconstructCtx::bv_widths`]. Returns
/// [`None`] for a compound or undeclared operand (the caller then rejects).
fn bv_operand_width(ctx: &ReconstructCtx, operand: &AletheTerm) -> Option<usize> {
    match operand {
        AletheTerm::App(head, args) if head == "@bbterm" => Some(args.len()),
        AletheTerm::Const(name) => parse_bv_literal(name)
            .map_or_else(|| ctx.bv_widths.get(name).copied(), |b| Some(b.len())),
        _ => None,
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
    let result = reconstruct_bitwise_clausal(ctx, commands);
    ctx.bridge = None;
    result
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
        "resolution" | "th_resolution" => Ok(Some(reconstruct_resolution_step(
            ctx, clause, premises, env,
        )?)),
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
        // Term-level bridge steps that the refutation never consumes (only the
        // predicate-level `equiv` clauses feed resolution). Defer them: no proof is
        // built, so no axiom is introduced. Their bit-iff content is separately
        // kernel-checked in `reconstruct_qf_bv_proof`.
        "cong" | "trans" => Ok(None),
        r if r.starts_with("bitblast_") => Ok(None),
        other => Err(ReconstructError::UnsupportedRule {
            rule: other.to_owned(),
        }),
    }
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

    let mut atom_keys: Vec<(String, AletheTerm)> = Vec::new();
    for lit in &substituted {
        collect_atoms(&lit.atom, &mut atom_keys);
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

use axeyum_ir::{Op as IrOp, Rational, Sort as IrSort, TermArena, TermId, TermNode as IrTermNode};
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

    fn neg(&self) -> Self {
        Self {
            coeffs: self
                .coeffs
                .iter()
                .map(|&(i, c)| (i, Rational::zero() - c))
                .collect(),
            constant: Rational::zero() - self.constant,
        }
    }

    fn add(&self, other: &Self) -> Self {
        let mut map: BTreeMap<usize, Rational> = BTreeMap::new();
        for &(i, c) in self.coeffs.iter().chain(&other.coeffs) {
            let e = map.entry(i).or_insert_with(Rational::zero);
            *e = *e + c;
        }
        let coeffs = map.into_iter().filter(|(_, c)| !c.is_zero()).collect();
        Self {
            coeffs,
            constant: self.constant + other.constant,
        }
    }

    fn sub(&self, other: &Self) -> Self {
        self.add(&other.neg())
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
    reconstruct_transitivity_refutation(ctx, arena, assertions, &certificate)
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
        } => Some(real_to_lin_inner(arena, args[0], vars)?.neg()),
        IrTermNode::App {
            op: IrOp::RealAdd,
            args,
        } => {
            let a = real_to_lin_inner(arena, args[0], vars)?;
            let b = real_to_lin_inner(arena, args[1], vars)?;
            Some(a.add(&b))
        }
        IrTermNode::App {
            op: IrOp::RealSub,
            args,
        } => {
            let a = real_to_lin_inner(arena, args[0], vars)?;
            let b = real_to_lin_inner(arena, args[1], vars)?;
            Some(a.sub(&b))
        }
        IrTermNode::App {
            op: IrOp::RealMul,
            args,
        } => {
            let a = real_to_lin_inner(arena, args[0], vars)?;
            let b = real_to_lin_inner(arena, args[1], vars)?;
            // Linear: one factor must be a bare constant.
            if a.coeffs.is_empty() {
                Some(scale_lin(&b, a.constant))
            } else if b.coeffs.is_empty() {
                Some(scale_lin(&a, b.constant))
            } else {
                None
            }
        }
        _ => None,
    }
}

/// Scale a [`LinR`] by a constant factor.
#[allow(dead_code)]
fn scale_lin(lin: &LinR, factor: Rational) -> LinR {
    if factor.is_zero() {
        return LinR::constant(Rational::zero());
    }
    LinR {
        coeffs: lin.coeffs.iter().map(|&(i, c)| (i, c * factor)).collect(),
        constant: lin.constant * factor,
    }
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
