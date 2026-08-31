//! A small, inspectable proof-plan IR (L3 phase D5,
//! `docs/plan/definition-discovery-efficiency-roadmap-2026-08-30.md`), compiled
//! to ordinary kernel terms above raw [`ExprId`] construction.
//!
//! ## The trust boundary — the kernel never sees a [`Plan`]
//!
//! [`compile`] walks a [`Plan`] value and calls the SAME public [`NatOps`]
//! builder methods (`congr`, `trans`, `symm`, `transport`, `const_app`, …)
//! that every hand-written `declare_*` function in this crate already calls.
//! The output is an ordinary [`ExprId`] proof term, handed to
//! [`NatOps::declare_theorem`]/[`Kernel::add_declaration`] exactly as a
//! hand-built term would be — the kernel's type-checker re-derives the proof
//! from scratch either way and has no notion of "plan" at all. A bug in a
//! [`Plan`] or in [`compile`] therefore produces a kernel REJECTION or a
//! proof of the wrong STATEMENT, never a false theorem past the trusted gate
//! — the identical argument ADR-0965 makes for the declarative declaration
//! spec pilot, carried over from *definitions with no proof body* to *proof
//! terms re-checked end to end*.
//!
//! This module is the compiler and nothing else. It does not:
//! - add a `Plan` variant to [`crate::env::Declaration`] — declarations stay
//!   `Definition`/`Theorem`/inductive exactly as today;
//! - skip [`Kernel::add_declaration`]'s own check — every [`compile`] output
//!   still goes through it;
//! - special-case anything at admission time based on how a term was built.
//!
//! ## Node set
//!
//! [`Plan`] has exactly the ten shapes L3 D5's exit criterion names: `Exact`
//! and `Apply` (raw construction and lemma application), `Rewrite` and
//! `Symmetry` (congruence and its transpose over `Eq` or `Iff` —
//! [`Rel`]), `Transitivity` (an n-ary chain that degenerates to a single
//! hand-written `trans`/`iff_trans` call at two steps, which is what keeps
//! the compiled term byte-identical to the code it replaces),
//! `Constructor` (`Eq.refl`, `Iff.intro`, `And.intro`), `Transport` (the bare
//! `Eq.rec` eliminator `Rewrite`/`Symmetry` are both special cases of),
//! `Eliminate` (a one-shot recursor case split), `Induction` (structural
//! `Nat.rec`), `Witness` (a single `Exists.intro`), and `Compute` (discharge
//! by definitional equality, checked against [`Kernel::def_eq`] BEFORE the
//! term is built — the node most likely to decline).
//!
//! [`Template`] is the one shared "motive" representation: a one-variable
//! term with the variable's occurrences marked by [`Template::Hole`]. Every
//! node that needs a motive (`Rewrite`, `Transport`, `Eliminate`,
//! `Induction`, `Witness`) uses it, so there is exactly one motive shape in
//! this IR, not five.
//!
//! ## What this IR deliberately leaves out
//!
//! - No general lambda/closure DSL: `Template` covers a named constant
//!   applied to fixed arguments with the variable repeated at zero or more
//!   positions (`fun x => add x x`, `fun x => dvd k x`, …). That is every
//!   motive the three rewritten families and the coverage tests need; a
//!   dependent motive over a compound scrutinee is out of scope, same as
//!   ADR-0965's interpreter DSL.
//! - `Induction`'s step still needs its own `j`/`ih` free variables minted
//!   by the CALLER before the `Plan` is built (`Plan::Induction`'s `j_fv`/
//!   `ih_fv` fields) — `NatOps::induct` mints them from inside its own
//!   closure and there is no way to hand it pre-existing ids, so
//!   reimplementing the `Nat.rec` application directly (rather than calling
//!   `induct`) is what lets a `Plan`'s step subtree reference them as
//!   ordinary [`Plan::Exact`] leaves.
//! - No serialization format. A `Plan` is an ordinary Rust value for this
//!   phase, not a wire format read from `artifacts/proof-plan/`; nothing here
//!   claims JSON round-tripping.

use crate::Kernel;
use crate::KernelError;
use crate::NatOps;
use crate::expr::ExprId;
use crate::name::NameId;

/// Which two-place logical connective a plan step reasons about. Both cases
/// end up calling the ordinary [`NatOps`] combinator for that connective
/// (`trans`/`symm` for `Eq`; the module-private `iff_trans`/`iff_symm` — the
/// same construction every `pred_iff_of_eq`/`iff_trans` local copy in this
/// crate already used by hand — for `Iff`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Rel {
    /// `Eq.{1} Nat _ _`.
    Eq,
    /// `Iff _ _`.
    Iff,
}

/// A one-variable term template: `Hole` marks every occurrence of the
/// variable, `Fixed` freezes an already-built subterm, `App` rebuilds a
/// constant application whose arguments are themselves templates. Applying
/// the SAME hole value at every occurrence gives the motive `fun x =>
/// template(x)` — this is the one motive representation every node in this
/// IR that needs one (`Rewrite`, `Transport`, `Eliminate`, `Induction`,
/// `Witness`) shares.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Template {
    /// The variable itself.
    Hole,
    /// An already-built subterm, independent of the variable.
    Fixed(ExprId),
    /// `name(args[0], args[1], …)`, each argument itself a template — a
    /// universe-MONOMORPHIC constant application (`NatOps::const_app`'s own
    /// restriction), which covers every prelude function/predicate name
    /// (`dvd`, `add`, …).
    App(NameId, Vec<Template>),
    /// `Eq.{1} Nat (left x) (right x)` — `Eq` is universe-polymorphic
    /// (`NatOps::eq` supplies the level argument `const_app` cannot), so it
    /// needs its own template shape rather than fitting `App`.
    EqNat(Box<Template>, Box<Template>),
}

impl Template {
    /// Instantiate every [`Template::Hole`] with `hole`.
    pub fn apply<D: NatOps>(&self, d: &mut D, hole: ExprId) -> ExprId {
        match self {
            Template::Hole => hole,
            Template::Fixed(e) => *e,
            Template::App(name, args) => {
                let built: Vec<ExprId> = args.iter().map(|a| a.apply(d, hole)).collect();
                d.const_app(*name, &built)
            }
            Template::EqNat(l, r) => {
                let lv = l.apply(d, hole);
                let rv = r.apply(d, hole);
                d.eq(lv, rv)
            }
        }
    }

    /// The closed motive `fun (x : Nat) => template(x)`.
    fn close<D: NatOps>(&self, d: &mut D) -> ExprId {
        let nat = d.nat_ty();
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let body = self.apply(d, x);
        d.lam_fv(x_fv, nat, body)
    }
}

/// A constructor/introduction leaf.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Ctor {
    /// `Eq.refl a`.
    Refl(ExprId),
    /// `Iff.intro mp mpr` at the stated propositions.
    IffIntro {
        /// The left proposition.
        a: ExprId,
        /// The right proposition.
        b: ExprId,
        /// A proof of `a -> b`.
        mp: Box<Plan>,
        /// A proof of `b -> a`.
        mpr: Box<Plan>,
    },
    /// `And.intro left right` at the stated propositions.
    AndIntro {
        /// The left conjunct.
        a: ExprId,
        /// The right conjunct.
        b: ExprId,
        /// A proof of `a`.
        left: Box<Plan>,
        /// A proof of `b`.
        right: Box<Plan>,
    },
}

/// The bounded proof-plan IR. See the module doc for the trust boundary and
/// what is deliberately out of scope. Every variant is plain data — no
/// closures anywhere in this type — so a `Plan` value can be built, matched
/// on, compared, and rendered for review before it is ever compiled.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Plan {
    /// An already-built term, used as-is: the escape hatch for ordinary
    /// value/statement construction that is not itself proof glue (a
    /// hypothesis free variable, a plain arithmetic subterm, a previously
    /// compiled sub-proof, …).
    Exact(ExprId),
    /// Apply a declared name (a lemma or a data constructor) to compiled
    /// argument plans, left-associated — `NatOps::const_app`.
    Apply {
        /// The declared name being applied.
        name: NameId,
        /// The (compiled) arguments, in order.
        args: Vec<Plan>,
    },
    /// Lift a proof of `Eq from to` through a one-hole context via
    /// congruence: `Eq (ctx from) (ctx to)` (`relation = Eq`, exactly
    /// `NatOps::congr`) or, when `ctx` is itself a `Prop`-valued predicate,
    /// `Iff (ctx from) (ctx to)` (`relation = Iff`, exactly the
    /// `pred_iff_of_eq` shape three `nat_prelude` files each hand-copied).
    Rewrite {
        /// `Eq` or `Iff`, deciding both the outer wrapper and how the
        /// automatic base case is built.
        relation: Rel,
        /// The one-hole context being lifted through.
        ctx: Template,
        /// The equality proof's left endpoint.
        from: ExprId,
        /// The equality proof's right endpoint.
        to: ExprId,
        /// A proof of `Eq from to`.
        eq: Box<Plan>,
    },
    /// Flip a proof of the stated relation between `a` and `b`.
    Symmetry {
        /// `Eq` or `Iff`.
        relation: Rel,
        /// The relation's left side.
        a: ExprId,
        /// The relation's right side.
        b: ExprId,
        /// A proof of the relation between `a` and `b`.
        of: Box<Plan>,
    },
    /// A left-folded chain `start ~ s0 ~ s1 ~ … ~ sn` under one relation. A
    /// single-step chain compiles to that step's own proof (no `trans` call
    /// at all); a two-step chain compiles to exactly one `trans`/`iff_trans`
    /// call over the two step proofs, matching a hand-written
    /// `d.trans(a, b, c, h1, h2)` term for term.
    Transitivity {
        /// `Eq` or `Iff`.
        relation: Rel,
        /// The chain's starting point.
        start: ExprId,
        /// `(endpoint, proof that the previous endpoint relates to it)`,
        /// in order.
        steps: Vec<(ExprId, Plan)>,
    },
    /// A constructor/introduction leaf.
    Constructor(Ctor),
    /// The general `Eq.rec` transport: given `eq : Eq from to` and a proof
    /// of `motive(from)`, produce a proof of `motive(to)`. `Rewrite` and
    /// `Symmetry` are both expressible as a `Transport` with an
    /// automatically-derived base case; this stays a separate node because
    /// most call sites reach for congruence, not the bare eliminator, and
    /// because some (`Nat.dist_eq_zero`'s `Eq.rec` along a hypothesis) need
    /// an arbitrary base proof rather than a self-evident one.
    Transport {
        /// The one-hole `motive(x)` being transported along.
        motive: Template,
        /// The equality proof's left endpoint.
        from: ExprId,
        /// The equality proof's right endpoint.
        to: ExprId,
        /// A proof of `Eq from to`.
        eq: Box<Plan>,
        /// A proof of `motive(from)`.
        base: Box<Plan>,
    },
    /// A one-shot recursor application (a case split, not a full
    /// induction): `recursor motive case_0 … case_{k-1} target`, minor
    /// premises in recursor argument order.
    Eliminate {
        /// The recursor being applied (e.g. `Bool.rec`).
        recursor: NameId,
        /// The (non-dependent-in-the-proof) motive.
        motive: Template,
        /// The minor premises, in the recursor's own argument order.
        cases: Vec<Plan>,
        /// The scrutinee.
        target: ExprId,
    },
    /// Structural `Nat.rec` at a `Prop`-valued motive: `base : motive(zero)`,
    /// `step` proves `motive(succ j)` given `ih : motive(j)`. `j_fv`/`ih_fv`
    /// are minted by the CALLER (`NatOps::fresh_fvar`) before `step` is
    /// built, so `step` refers to them as `Plan::Exact` leaves — see the
    /// module doc for why this node cannot simply delegate to
    /// `NatOps::induct`.
    Induction {
        /// The motive being inducted over.
        motive: Template,
        /// A proof of `motive(zero)`.
        base: Box<Plan>,
        /// The fvar id the caller minted for the induction variable `j`.
        j_fv: u64,
        /// The fvar id the caller minted for the induction hypothesis `ih`.
        ih_fv: u64,
        /// A proof of `motive(succ j)`, referring to `j_fv`/`ih_fv`.
        step: Box<Plan>,
        /// The scrutinee.
        target: ExprId,
    },
    /// A single existential introduction: `∃ x, predicate(x)` from a
    /// concrete `value` and a proof of `predicate(value)`.
    Witness {
        /// The one-hole predicate `predicate(x)`.
        predicate: Template,
        /// The witness value.
        value: ExprId,
        /// A proof of `predicate(value)`.
        proof: Box<Plan>,
    },
    /// Discharge `Eq lhs rhs` by definitional equality alone, checked
    /// against [`Kernel::def_eq`] BEFORE any term is built — the "checked
    /// computation" node, and the one this compiler declines most directly:
    /// a `Compute` step whose two sides are not defeq never reaches
    /// `Eq.refl`, let alone `add_declaration`.
    Compute {
        /// The left-hand side.
        lhs: ExprId,
        /// The right-hand side, claimed definitionally equal to `lhs`.
        rhs: ExprId,
    },
}

/// Why [`compile`] or [`theorem_plan`] refused a [`Plan`] before it ever
/// reached the kernel's trusted gate.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PlanError {
    /// A `Compute` step claimed two terms are definitionally equal and
    /// [`Kernel::def_eq`] disagreed.
    NotDefEq {
        /// The left-hand side.
        lhs: ExprId,
        /// The right-hand side.
        rhs: ExprId,
    },
    /// A `Transitivity` chain with zero steps: there is nothing relating
    /// `start` to anything, so no proof can be produced.
    EmptyChain,
    /// An `Eliminate` step was handed zero cases.
    NoCases,
    /// The compiled term still mentions a free variable no enclosing plan
    /// node bound — the `UnboundFVar` class of bug this phase's brief calls
    /// out (`d.arrow` where `d.pi_fv` was needed), caught here with a typed
    /// reason instead of surfacing as the kernel's opaque
    /// `KernelError::UnboundFVar { id }`.
    UnboundFreeVariable {
        /// Where the leak was caught (`"final theorem type"` or
        /// `"final theorem value"`).
        site: &'static str,
    },
}

/// Either [`compile`]/[`theorem_plan`] declined the plan itself, or the
/// kernel's trusted gate rejected the resulting term.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PlanOutcome {
    /// The plan was malformed; the kernel was never asked.
    Declined(PlanError),
    /// The plan compiled to a term, and `add_declaration` refused it.
    Rejected(KernelError),
}

// --- Iff combinators, shared by every `Rel::Iff` node -----------------------
//
// These are the SAME construction as the `pred_iff_of_eq`/`iff_trans` pair
// duplicated by hand in (at least) `dvd_add_iff_left.rs`, `gcd_dvd_mirrors.rs`
// and `gcd_mul_right_mirrors.rs` (each file's module doc calls this out as a
// deliberate "local copy" convention) — written once here so `Rel::Iff`
// compiles to a term shaped identically to what those files built by hand.

/// `h : Iff a b ⊢ Iff b a`.
fn iff_symm<D: NatOps>(d: &mut D, a: ExprId, b: ExprId, h: ExprId) -> ExprId {
    let logic = d.prelude().logic;
    let mp = d.const_app(logic.iff_mpr, &[a, b, h]);
    let mpr = d.const_app(logic.iff_mp, &[a, b, h]);
    d.const_app(logic.iff_intro, &[b, a, mp, mpr])
}

/// `h1 : Iff a b, h2 : Iff b c ⊢ Iff a c`.
fn iff_trans<D: NatOps>(
    d: &mut D,
    a: ExprId,
    b: ExprId,
    c: ExprId,
    h1: ExprId,
    h2: ExprId,
) -> ExprId {
    let logic = d.prelude().logic;
    let mp = {
        let a_fv = d.fresh_fvar();
        let av = d.kernel().fvar(a_fv);
        let h1_mp = d.const_app(logic.iff_mp, &[a, b, h1]);
        let b_from_a = d.apply(h1_mp, &[av]);
        let h2_mp = d.const_app(logic.iff_mp, &[b, c, h2]);
        let c_from_b = d.apply(h2_mp, &[b_from_a]);
        d.lam_fv(a_fv, a, c_from_b)
    };
    let mpr = {
        let c_fv = d.fresh_fvar();
        let cv = d.kernel().fvar(c_fv);
        let h2_mpr = d.const_app(logic.iff_mpr, &[b, c, h2]);
        let b_from_c = d.apply(h2_mpr, &[cv]);
        let h1_mpr = d.const_app(logic.iff_mpr, &[a, b, h1]);
        let a_from_b = d.apply(h1_mpr, &[b_from_c]);
        d.lam_fv(c_fv, c, a_from_b)
    };
    d.const_app(logic.iff_intro, &[a, c, mp, mpr])
}

/// `Iff.intro id id : Iff fa fa` — the `Rel::Iff` self-proof `Transport`'s
/// automatically-derived base case uses.
fn iff_self_intro<D: NatOps>(d: &mut D, fa: ExprId) -> ExprId {
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);
    let id = d.lam_fv(h_fv, fa, h);
    let name = d.prelude().logic.iff_intro;
    d.const_app(name, &[fa, fa, id, id])
}

impl Rel {
    fn trans<D: NatOps>(
        self,
        d: &mut D,
        a: ExprId,
        b: ExprId,
        c: ExprId,
        h1: ExprId,
        h2: ExprId,
    ) -> ExprId {
        match self {
            Rel::Eq => d.trans(a, b, c, h1, h2),
            Rel::Iff => iff_trans(d, a, b, c, h1, h2),
        }
    }

    fn symm<D: NatOps>(self, d: &mut D, a: ExprId, b: ExprId, h: ExprId) -> ExprId {
        match self {
            Rel::Eq => d.symm(a, b, h),
            Rel::Iff => iff_symm(d, a, b, h),
        }
    }
}

/// Compile a [`Plan`] into an ordinary kernel proof term by calling the same
/// [`NatOps`] builder methods hand-written proof code calls. Declines with a
/// typed [`PlanError`] before building anything the caller asked to be
/// checked ([`Plan::Compute`], an empty [`Plan::Transitivity`], an empty
/// [`Plan::Eliminate`]); every other malformation surfaces as the kernel's
/// own rejection once the caller passes the result to
/// [`NatOps::declare_theorem`].
///
/// # Errors
///
/// Returns [`PlanError`] if the plan itself is malformed (see [`PlanError`]'s
/// variants). Does not call the kernel's trusted gate — that is the caller's
/// job, exactly as it is for a hand-built term.
pub fn compile<D: NatOps>(plan: &Plan, d: &mut D) -> Result<ExprId, PlanError> {
    match plan {
        Plan::Exact(e) => Ok(*e),
        Plan::Apply { name, args } => {
            let mut built = Vec::with_capacity(args.len());
            for a in args {
                built.push(compile(a, d)?);
            }
            Ok(d.const_app(*name, &built))
        }
        Plan::Constructor(c) => compile_ctor(c, d),
        Plan::Compute { lhs, rhs } => {
            if !d.kernel().def_eq(*lhs, *rhs) {
                return Err(PlanError::NotDefEq {
                    lhs: *lhs,
                    rhs: *rhs,
                });
            }
            Ok(d.refl(*lhs))
        }
        Plan::Transport {
            motive,
            from,
            to,
            eq,
            base,
        } => {
            let eq_term = compile(eq, d)?;
            let base_term = compile(base, d)?;
            let motive_term = motive.close(d);
            Ok(d.transport(*from, motive_term, base_term, *to, eq_term))
        }
        Plan::Rewrite {
            relation,
            ctx,
            from,
            to,
            eq,
        } => {
            let eq_term = compile(eq, d)?;
            match relation {
                Rel::Eq => Ok(d.congr(*from, *to, eq_term, &|d, x| ctx.apply(d, x))),
                Rel::Iff => {
                    let fa = ctx.apply(d, *from);
                    let motive = d.eq_motive(*from, &|d, x| {
                        let fx = ctx.apply(d, x);
                        let iff = d.prelude().logic.iff;
                        d.const_app(iff, &[fa, fx])
                    });
                    let base_term = iff_self_intro(d, fa);
                    Ok(d.transport(*from, motive, base_term, *to, eq_term))
                }
            }
        }
        Plan::Symmetry { relation, a, b, of } => {
            let h = compile(of, d)?;
            Ok(relation.symm(d, *a, *b, h))
        }
        Plan::Transitivity {
            relation,
            start,
            steps,
        } => {
            let mut iter = steps.iter();
            let (first_end, first_plan) = iter.next().ok_or(PlanError::EmptyChain)?;
            let mut proof = compile(first_plan, d)?;
            let mut current = *first_end;
            for (next, step_plan) in iter {
                let step_proof = compile(step_plan, d)?;
                proof = relation.trans(d, *start, current, *next, proof, step_proof);
                current = *next;
            }
            Ok(proof)
        }
        Plan::Eliminate {
            recursor,
            motive,
            cases,
            target,
        } => {
            if cases.is_empty() {
                return Err(PlanError::NoCases);
            }
            let mut case_terms = Vec::with_capacity(cases.len());
            for c in cases {
                case_terms.push(compile(c, d)?);
            }
            let motive_term = motive.close(d);
            let z = d.kernel().level_zero();
            let rec = d.kernel().const_(*recursor, vec![z]);
            let mut args = vec![motive_term];
            args.extend(case_terms);
            args.push(*target);
            Ok(d.apply(rec, &args))
        }
        Plan::Induction {
            motive,
            base,
            j_fv,
            ih_fv,
            step,
            target,
        } => {
            let nat = d.nat_ty();
            let motive_term = motive.close(d);
            let base_term = compile(base, d)?;
            let step_term = {
                let j = d.kernel().fvar(*j_fv);
                let hyp_ty = motive.apply(d, j);
                let body = compile(step, d)?;
                let inner = d.lam_fv(*ih_fv, hyp_ty, body);
                d.lam_fv(*j_fv, nat, inner)
            };
            let z = d.kernel().level_zero();
            let rec_name = d.prelude().rec;
            let rec = d.kernel().const_(rec_name, vec![z]);
            Ok(d.apply(rec, &[motive_term, base_term, step_term, *target]))
        }
        Plan::Witness {
            predicate,
            value,
            proof,
        } => {
            let proof_term = compile(proof, d)?;
            let nat = d.nat_ty();
            let one = d.level_one();
            let pred_term = predicate.close(d);
            let intro_name = d.prelude().logic.exists_intro;
            let intro = d.kernel().const_(intro_name, vec![one]);
            Ok(d.apply(intro, &[nat, pred_term, *value, proof_term]))
        }
    }
}

fn compile_ctor<D: NatOps>(c: &Ctor, d: &mut D) -> Result<ExprId, PlanError> {
    match c {
        Ctor::Refl(a) => Ok(d.refl(*a)),
        Ctor::IffIntro { a, b, mp, mpr } => {
            let mp_t = compile(mp, d)?;
            let mpr_t = compile(mpr, d)?;
            let name = d.prelude().logic.iff_intro;
            Ok(d.const_app(name, &[*a, *b, mp_t, mpr_t]))
        }
        Ctor::AndIntro { a, b, left, right } => {
            let l = compile(left, d)?;
            let r = compile(right, d)?;
            let name = d.prelude().logic.and_intro;
            Ok(d.const_app(name, &[*a, *b, l, r]))
        }
    }
}

/// Declare `theorem name : ∀ (x_0 … x_{arity-1} : Nat), stmt := fun … =>
/// proof`, where `build` returns the statement via ordinary term
/// construction and the proof as a [`Plan`] — the [`Plan`]-based sibling of
/// [`NatOps::try_theorem`]. Compiles the plan, then — unlike `try_theorem`,
/// which trusts `add_declaration` to catch a leaked free variable as an
/// opaque `KernelError::UnboundFVar` — checks the fully-bound type and value
/// for a leak with [`Kernel::has_fvars`] and declines with a named
/// [`PlanError::UnboundFreeVariable`] before the kernel is ever asked.
///
/// # Errors
///
/// Returns [`PlanOutcome::Declined`] if the plan itself was malformed, or
/// [`PlanOutcome::Rejected`] if the kernel's trusted gate refused the
/// resulting term.
pub fn theorem_plan<D: NatOps>(
    d: &mut D,
    name: NameId,
    arity: usize,
    build: &dyn Fn(&mut D, &[ExprId]) -> (ExprId, Plan),
) -> Result<ExprId, PlanOutcome> {
    let nat = d.nat_ty();
    let fvs: Vec<u64> = (0..arity).map(|_| d.fresh_fvar()).collect();
    let vars: Vec<ExprId> = fvs.iter().map(|&f| d.kernel().fvar(f)).collect();
    let (stmt, plan) = build(d, &vars);
    let proof = compile(&plan, d).map_err(PlanOutcome::Declined)?;

    let mut ty = stmt;
    let mut value = proof;
    for &fv in fvs.iter().rev() {
        ty = d.pi_fv(fv, nat, ty);
        value = d.lam_fv(fv, nat, value);
    }

    if d.kernel().has_fvars(ty) {
        return Err(PlanOutcome::Declined(PlanError::UnboundFreeVariable {
            site: "final theorem type",
        }));
    }
    if d.kernel().has_fvars(value) {
        return Err(PlanOutcome::Declined(PlanError::UnboundFreeVariable {
            site: "final theorem value",
        }));
    }

    d.declare_theorem(name, ty, value)
        .map_err(PlanOutcome::Rejected)?;
    Ok(ty)
}

// --- one-line convenience wrappers ------------------------------------------
//
// `compile` plus the `Plan` struct literals above is the full, inspectable
// IR. These three are thin wrappers around the single most-repeated shape in
// the crate — the `pred_iff_of_eq`/`iff_trans`/`iff_symm` trio at least three
// `nat_prelude` files hand-copied — restoring a one-line call at use sites
// while still routing through `compile` and the same `Plan::Rewrite`/
// `Transitivity`/`Symmetry` nodes underneath: nothing here bypasses the
// compiler, it only saves callers from spelling out a struct literal for the
// overwhelmingly common case. `Plan::Exact` wraps each already-built `ExprId`
// argument for them.

/// Lift `eq : Eq from to` through the one-hole `Prop`-valued context `ctx`
/// into `Iff (ctx from) (ctx to)` — the `pred_iff_of_eq` shape.
pub fn iff_lift<D: NatOps>(
    d: &mut D,
    ctx: Template,
    from: ExprId,
    to: ExprId,
    eq: ExprId,
) -> ExprId {
    compile(
        &Plan::Rewrite {
            relation: Rel::Iff,
            ctx,
            from,
            to,
            eq: Box::new(Plan::Exact(eq)),
        },
        d,
    )
    .expect("Rewrite[Iff] over an Eq proof and a Template context is always well-formed")
}

/// Chain `start ~ s0 ~ s1 ~ … ~ sn` under `Iff` — the `iff_trans` shape,
/// generalized to any nonzero step count. `steps` must be nonempty.
pub fn iff_chain<D: NatOps>(d: &mut D, start: ExprId, steps: &[(ExprId, ExprId)]) -> ExprId {
    let steps = steps
        .iter()
        .map(|&(next, proof)| (next, Plan::Exact(proof)))
        .collect();
    compile(
        &Plan::Transitivity {
            relation: Rel::Iff,
            start,
            steps,
        },
        d,
    )
    .expect("iff_chain requires a nonempty `steps` slice")
}

/// `h : Iff a b ⊢ Iff b a` — the `iff_symm` shape.
pub fn iff_flip<D: NatOps>(d: &mut D, a: ExprId, b: ExprId, h: ExprId) -> ExprId {
    compile(
        &Plan::Symmetry {
            relation: Rel::Iff,
            a,
            b,
            of: Box::new(Plan::Exact(h)),
        },
        d,
    )
    .expect("Symmetry[Iff] is always well-formed")
}

// --- rendering, for review --------------------------------------------------

impl Template {
    /// A one-line rendering: `Hole` as `_`, `Fixed` as its rendered Lean
    /// term, `App` as `name(arg, arg, …)`.
    pub fn render(&self, k: &Kernel) -> String {
        match self {
            Template::Hole => "_".to_string(),
            Template::Fixed(e) => k.render_lean(*e),
            Template::App(name, args) => {
                let rendered: Vec<String> = args.iter().map(|a| a.render(k)).collect();
                format!("{}({})", k.lean_name(*name), rendered.join(", "))
            }
            Template::EqNat(l, r) => format!("Eq({}, {})", l.render(k), r.render(k)),
        }
    }
}

impl Plan {
    /// An indented multi-line rendering of the plan's node structure, for
    /// human review before (or after) compiling. Leaves render the `ExprId`
    /// they carry through [`Kernel::render_lean`]; every node names its own
    /// kind, so the ten shapes this IR distinguishes are visible in the
    /// output rather than folded into one generic "term" line.
    pub fn render(&self, k: &Kernel) -> String {
        let mut out = String::new();
        self.render_into(k, 0, &mut out);
        out
    }

    fn render_into(&self, k: &Kernel, depth: usize, out: &mut String) {
        let pad = "  ".repeat(depth);
        match self {
            Plan::Exact(e) => {
                out.push_str(&format!("{pad}Exact: {}\n", k.render_lean(*e)));
            }
            Plan::Apply { name, args } => {
                out.push_str(&format!("{pad}Apply: {}\n", k.lean_name(*name)));
                for a in args {
                    a.render_into(k, depth + 1, out);
                }
            }
            Plan::Rewrite {
                relation,
                ctx,
                from,
                to,
                eq,
            } => {
                out.push_str(&format!(
                    "{pad}Rewrite[{relation:?}]: ctx = fun x => {}, {} -> {}\n",
                    ctx.render(k),
                    k.render_lean(*from),
                    k.render_lean(*to)
                ));
                eq.render_into(k, depth + 1, out);
            }
            Plan::Symmetry { relation, a, b, of } => {
                out.push_str(&format!(
                    "{pad}Symmetry[{relation:?}]: {} <-> {}\n",
                    k.render_lean(*a),
                    k.render_lean(*b)
                ));
                of.render_into(k, depth + 1, out);
            }
            Plan::Transitivity {
                relation,
                start,
                steps,
            } => {
                out.push_str(&format!(
                    "{pad}Transitivity[{relation:?}]: start = {}\n",
                    k.render_lean(*start)
                ));
                for (next, step) in steps {
                    out.push_str(&format!("{pad}  -> {}\n", k.render_lean(*next)));
                    step.render_into(k, depth + 2, out);
                }
            }
            Plan::Constructor(c) => {
                out.push_str(&format!("{pad}Constructor\n"));
                match c {
                    Ctor::Refl(a) => {
                        out.push_str(&format!("{pad}  Refl: {}\n", k.render_lean(*a)));
                    }
                    Ctor::IffIntro { mp, mpr, .. } => {
                        out.push_str(&format!("{pad}  IffIntro.mp\n"));
                        mp.render_into(k, depth + 2, out);
                        out.push_str(&format!("{pad}  IffIntro.mpr\n"));
                        mpr.render_into(k, depth + 2, out);
                    }
                    Ctor::AndIntro { left, right, .. } => {
                        out.push_str(&format!("{pad}  AndIntro.left\n"));
                        left.render_into(k, depth + 2, out);
                        out.push_str(&format!("{pad}  AndIntro.right\n"));
                        right.render_into(k, depth + 2, out);
                    }
                }
            }
            Plan::Transport {
                motive,
                from,
                to,
                eq,
                base,
            } => {
                out.push_str(&format!(
                    "{pad}Transport: motive = fun x => {}, {} -> {}\n",
                    motive.render(k),
                    k.render_lean(*from),
                    k.render_lean(*to)
                ));
                out.push_str(&format!("{pad}  eq:\n"));
                eq.render_into(k, depth + 2, out);
                out.push_str(&format!("{pad}  base:\n"));
                base.render_into(k, depth + 2, out);
            }
            Plan::Eliminate {
                recursor,
                motive,
                cases,
                target,
            } => {
                out.push_str(&format!(
                    "{pad}Eliminate[{}]: motive = fun x => {}, target = {}\n",
                    k.lean_name(*recursor),
                    motive.render(k),
                    k.render_lean(*target)
                ));
                for (i, c) in cases.iter().enumerate() {
                    out.push_str(&format!("{pad}  case {i}:\n"));
                    c.render_into(k, depth + 2, out);
                }
            }
            Plan::Induction {
                motive,
                base,
                target,
                ..
            } => {
                out.push_str(&format!(
                    "{pad}Induction: motive = fun x => {}, target = {}\n",
                    motive.render(k),
                    k.render_lean(*target)
                ));
                out.push_str(&format!("{pad}  base:\n"));
                base.render_into(k, depth + 2, out);
                out.push_str(&format!(
                    "{pad}  step: <bound to j_fv/ih_fv, rendered below>\n"
                ));
            }
            Plan::Witness {
                predicate,
                value,
                proof,
            } => {
                out.push_str(&format!(
                    "{pad}Witness: predicate = fun x => {}, value = {}\n",
                    predicate.render(k),
                    k.render_lean(*value)
                ));
                proof.render_into(k, depth + 1, out);
            }
            Plan::Compute { lhs, rhs } => {
                out.push_str(&format!(
                    "{pad}Compute: {} == {}\n",
                    k.render_lean(*lhs),
                    k.render_lean(*rhs)
                ));
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{NatDev, NatPrelude, build_nat_prelude};

    fn dev() -> (Kernel, NatPrelude) {
        let mut k = Kernel::new();
        let p = build_nat_prelude(&mut k).expect("Nat prelude must build");
        (k, p)
    }

    /// `Rewrite[Eq]` reproduces `NatOps::congr` on a genuine two-hole
    /// template (`add x x`, the shape `dist_self` needs) — the positive
    /// control every decline test below is checked against.
    #[test]
    fn rewrite_eq_congr_matches_hand_built() {
        let (mut k, p) = dev();
        let mut d = NatDev::new(&mut k, p);
        let n = d.num(3);
        let m = d.num(3); // same numeral: n and m intern to the SAME ExprId.
        let eq_nm = d.refl(n); // Eq n n, reused as "Eq n m" since n == m here.

        let ctx = Template::App(p.add, vec![Template::Hole, Template::Hole]);
        let plan = Plan::Rewrite {
            relation: Rel::Eq,
            ctx: ctx.clone(),
            from: n,
            to: m,
            eq: Box::new(Plan::Exact(eq_nm)),
        };
        let compiled = compile(&plan, &mut d).expect("well-formed rewrite must compile");
        let hand = d.congr(n, m, eq_nm, &|d, x| d.add(x, x));
        assert_eq!(
            compiled, hand,
            "compiled Rewrite must match NatOps::congr exactly"
        );
        // And it must actually check.
        let ty = d
            .kernel()
            .infer(compiled)
            .expect("compiled proof must type-check");
        let nn = d.add(n, n);
        let mm = d.add(m, m);
        let expected_ty = d.eq(nn, mm);
        assert!(d.kernel().def_eq(ty, expected_ty));
    }

    /// The real shortening case: `Rewrite[Iff]` reproduces the
    /// `pred_iff_of_eq(d, &p, a, b, eq_ab, |d, v| d.dvd(k, v))` shape used
    /// (as a hand-copied local function) in `dvd_add_iff_left.rs`,
    /// `gcd_dvd_mirrors.rs`, and `gcd_mul_right_mirrors.rs`.
    #[test]
    fn rewrite_iff_matches_pred_iff_of_eq() {
        let (mut k, p) = dev();
        let mut d = NatDev::new(&mut k, p);
        let a = d.num(2);
        let b = d.num(2);
        let eq_ab = d.refl(a);
        let kk = d.num(5);

        let ctx = Template::App(p.dvd, vec![Template::Fixed(kk), Template::Hole]);
        let plan = Plan::Rewrite {
            relation: Rel::Iff,
            ctx,
            from: a,
            to: b,
            eq: Box::new(Plan::Exact(eq_ab)),
        };
        let compiled = compile(&plan, &mut d).expect("well-formed iff-rewrite must compile");

        // Hand-built `pred_iff_of_eq` (verbatim, mirroring the three files).
        let pa = d.dvd(kk, a);
        let motive = d.eq_motive(a, &|d, x| {
            let px = d.dvd(kk, x);
            let iff = d.prelude().logic.iff;
            d.const_app(iff, &[pa, px])
        });
        let refl_case = {
            let x_fv = d.fresh_fvar();
            let x = d.kernel().fvar(x_fv);
            let id = d.lam_fv(x_fv, pa, x);
            let iff_intro = d.prelude().logic.iff_intro;
            d.const_app(iff_intro, &[pa, pa, id, id])
        };
        let hand = d.transport(a, motive, refl_case, b, eq_ab);

        assert_eq!(
            compiled, hand,
            "compiled Rewrite[Iff] must match the hand-built pred_iff_of_eq shape exactly"
        );
    }

    /// `Transitivity` at exactly two steps compiles to a SINGLE `trans` call
    /// over the two step proofs — not the generic left-fold seeded with a
    /// spurious self-`refl` first step — which is what keeps it
    /// byte-identical to `d.trans(a, b, c, h1, h2)`.
    #[test]
    fn transitivity_two_steps_is_one_trans_call() {
        let (mut k, p) = dev();
        let mut d = NatDev::new(&mut k, p);
        let a = d.num(1);
        let b = d.num(2);
        let c = d.num(3);
        // Fabricate two Eq proofs between DISTINCT numerals via `refl` at a
        // shared point; only shape identity matters for this test, not truth.
        let h1 = d.refl(a); // pretend : Eq a b (untrue, but well-typed once b:=a)
        let h2 = d.refl(a); // pretend : Eq b c
        let plan = Plan::Transitivity {
            relation: Rel::Eq,
            start: a,
            steps: vec![(b, Plan::Exact(h1)), (c, Plan::Exact(h2))],
        };
        let compiled = compile(&plan, &mut d).expect("two-step chain must compile");
        let hand = d.trans(a, b, c, h1, h2);
        assert_eq!(compiled, hand);
    }

    /// A single-step chain compiles to that step's own proof, with no
    /// `trans` wrapper at all.
    #[test]
    fn transitivity_one_step_is_the_step_itself() {
        let (mut k, p) = dev();
        let mut d = NatDev::new(&mut k, p);
        let a = d.num(1);
        let b = d.num(1);
        let h = d.refl(a);
        let plan = Plan::Transitivity {
            relation: Rel::Eq,
            start: a,
            steps: vec![(b, Plan::Exact(h))],
        };
        let compiled = compile(&plan, &mut d).expect("one-step chain must compile");
        assert_eq!(compiled, h);
    }

    // --- malformed plans decline, observed ----------------------------------

    #[test]
    fn empty_transitivity_chain_declines() {
        let (mut k, p) = dev();
        let mut d = NatDev::new(&mut k, p);
        let a = d.num(0);
        let plan = Plan::Transitivity {
            relation: Rel::Eq,
            start: a,
            steps: vec![],
        };
        let err = compile(&plan, &mut d).expect_err("an empty chain proves nothing");
        assert_eq!(err, PlanError::EmptyChain);
    }

    #[test]
    fn eliminate_with_no_cases_declines() {
        let (mut k, p) = dev();
        let mut d = NatDev::new(&mut k, p);
        let target = d.num(0);
        let plan = Plan::Eliminate {
            recursor: p.rec,
            motive: Template::Fixed(d.nat_ty()),
            cases: vec![],
            target,
        };
        let err =
            compile(&plan, &mut d).expect_err("a recursor with no minor premises cannot apply");
        assert_eq!(err, PlanError::NoCases);
    }

    /// The headline malformed-plan case: a `Compute` step whose two sides are
    /// NOT definitionally equal declines with a named reason, checked
    /// against `Kernel::def_eq` before any `Eq.refl` term is even built.
    #[test]
    fn compute_on_non_defeq_terms_declines() {
        let (mut k, p) = dev();
        let mut d = NatDev::new(&mut k, p);
        let two = d.num(2);
        let three = d.num(3);
        let plan = Plan::Compute {
            lhs: two,
            rhs: three,
        };
        let err = compile(&plan, &mut d).expect_err("2 and 3 are not defeq");
        assert_eq!(
            err,
            PlanError::NotDefEq {
                lhs: two,
                rhs: three
            }
        );
    }

    /// The positive control for the above: equal numerals compute.
    #[test]
    fn compute_on_defeq_terms_succeeds() {
        let (mut k, p) = dev();
        let mut d = NatDev::new(&mut k, p);
        let two_a = d.num(2);
        let two_b = d.num(2);
        let plan = Plan::Compute {
            lhs: two_a,
            rhs: two_b,
        };
        let compiled = compile(&plan, &mut d).expect("2 == 2 is defeq");
        assert_eq!(compiled, d.refl(two_a));
    }

    /// `theorem_plan` catches a leaked free variable — the `UnboundFVar`
    /// class of bug from a hypothesis built with `d.arrow` instead of
    /// `d.pi_fv` — as a named `PlanError` before the kernel is asked at all.
    /// This is the compile-time check the phase brief asks for: the plan
    /// hands back a "proof" that is just the unbound hypothesis variable
    /// itself, with no enclosing binder to abstract it away.
    #[test]
    fn theorem_plan_declines_a_leaked_free_variable() {
        let (mut k, p) = dev();
        let mut d = NatDev::new(&mut k, p);
        let anon = d.anon_name();
        let name = d.kernel().name_str(anon, "proof_plan_leak_probe");
        let outcome = theorem_plan(&mut d, name, 0, &|d, _v| {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let nat = d.nat_ty();
            (nat, Plan::Exact(h))
        });
        assert_eq!(
            outcome,
            Err(PlanOutcome::Declined(PlanError::UnboundFreeVariable {
                site: "final theorem value"
            }))
        );
    }

    /// The positive control for the guard above: a genuine, closed
    /// `theorem_plan` declaration succeeds and is admitted by the kernel.
    #[test]
    fn theorem_plan_admits_a_well_formed_declaration() {
        let (mut k, p) = dev();
        let mut d = NatDev::new(&mut k, p);
        let anon = d.anon_name();
        let name = d.kernel().name_str(anon, "proof_plan_add_zero_refl_probe");
        let ty = theorem_plan(&mut d, name, 1, &|d, v| {
            let n = v[0];
            let zero = d.zero();
            let add_n0 = d.add(n, zero);
            let stmt = d.eq(add_n0, n);
            (stmt, Plan::Constructor(Ctor::Refl(add_n0)))
        })
        .expect("a genuine closed proof must be admitted");
        let _ = ty;
    }
}
