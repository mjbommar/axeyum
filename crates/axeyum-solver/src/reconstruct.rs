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
    /// Monotone counter for generating fresh, collision-free declaration names
    /// under a private namespace, so reconstructed atoms never clash with the
    /// prelude's names.
    next_id: u64,
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
    Ok(ctx.kernel.const_(name, vec![]))
}

#[cfg(test)]
mod tests;
