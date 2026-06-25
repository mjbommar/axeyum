//! The property entry point: declare symbolic inputs, optionally assume a
//! precondition, then `check` a Boolean property and get a `Proved` /
//! `Counterexample` / `Unknown` [`Outcome`].
//!
//! `check` lowers the bounds and precondition as **hypotheses** and the property
//! as the **goal**, then calls [`axeyum_solver::prove`] (which refutes
//! `hyps ∧ ¬goal` and *already re-checks* any certificate). `Proved` carries the
//! re-checked [`axeyum_solver::EvidenceReport`]; `Disproved(model)` is lifted
//! back into the user's typed input `T`; `Unknown` is surfaced verbatim.

use std::marker::PhantomData;

use axeyum_ir::{Op, SymbolId, TermArena, TermId, TermNode, Value};
use axeyum_solver::{
    EvidenceReport, ProofOutcome, SolverConfig, SolverError, UnknownReason, prove,
    prove_unsat_to_lean_module,
};

use crate::ctx::Ctx;
use crate::handle::{Bool, Bv, Int};

/// A declared symbolic input slot: the symbol id (for model lifting) and the
/// sort discriminator that says how to decode its [`Value`] back into `T`.
///
/// Appears only in the [`Symbolic::fresh`] signature, where each implementation
/// pushes one slot per leaf symbol it declares; its fields are private.
#[derive(Clone, Copy)]
pub struct Slot {
    sym: SymbolId,
    kind: SlotKind,
}

#[derive(Clone, Copy)]
enum SlotKind {
    Bv,
    Int,
    Bool,
}

/// The lifted, concrete value of a single symbolic input, decoded from a model.
///
/// This is the leaf the [`Symbolic::lift`] reconstruction is built from; users
/// receive a fully-typed `T` (e.g. a tuple of these), not this enum.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Lifted {
    /// A bit-vector input as `(width, value)`.
    Bv {
        /// Width in bits.
        width: u32,
        /// The value, masked to `width` bits.
        value: u128,
    },
    /// An integer input.
    Int(i128),
    /// A Boolean input.
    Bool(bool),
}

/// A symbolic input type: knows how to declare fresh solver symbols (the
/// `Arbitrary` analogue) and how to lift a counterexample's [`Lifted`] leaves
/// back into a concrete value of itself.
///
/// Implemented for the scalar handles ([`Bv`], [`Int`], [`Bool`]) and tuples of
/// them up to arity 3. The associated [`Symbolic::Concrete`] is the type a
/// `Counterexample` carries (e.g. `(u64, u64)` for `(Bv<64>, Bv<64>)`).
pub trait Symbolic<'c>: Sized {
    /// The concrete (non-symbolic) value carried by a counterexample.
    type Concrete;

    /// Declares the fresh symbolic inputs into `ctx`, pushing one [`Slot`] per
    /// leaf symbol (in left-to-right order) onto `slots`, and returns the
    /// symbolic handle(s).
    fn fresh(ctx: &'c Ctx, slots: &mut Vec<Slot>) -> Self;

    /// Reconstructs the concrete value from the lifted leaves (consumed
    /// left-to-right via the iterator), matching `fresh`'s push order.
    fn lift(leaves: &mut impl Iterator<Item = Lifted>) -> Self::Concrete;
}

impl<'c, const W: u32> Symbolic<'c> for Bv<'c, W> {
    type Concrete = u128;

    fn fresh(ctx: &'c Ctx, slots: &mut Vec<Slot>) -> Self {
        let (sym, term) = ctx.declare_bv(W);
        slots.push(Slot {
            sym,
            kind: SlotKind::Bv,
        });
        Bv::wrap(ctx, term)
    }

    fn lift(leaves: &mut impl Iterator<Item = Lifted>) -> Self::Concrete {
        match leaves.next() {
            Some(Lifted::Bv { value, .. }) => value,
            other => panic!("Bv::lift expected a bit-vector leaf, got {other:?}"),
        }
    }
}

impl<'c> Symbolic<'c> for Int<'c> {
    type Concrete = i128;

    fn fresh(ctx: &'c Ctx, slots: &mut Vec<Slot>) -> Self {
        let (sym, term) = ctx.declare_int();
        slots.push(Slot {
            sym,
            kind: SlotKind::Int,
        });
        Int::wrap(ctx, term)
    }

    fn lift(leaves: &mut impl Iterator<Item = Lifted>) -> Self::Concrete {
        match leaves.next() {
            Some(Lifted::Int(v)) => v,
            other => panic!("Int::lift expected an integer leaf, got {other:?}"),
        }
    }
}

impl<'c> Symbolic<'c> for Bool<'c> {
    type Concrete = bool;

    fn fresh(ctx: &'c Ctx, slots: &mut Vec<Slot>) -> Self {
        let (sym, term) = ctx.declare_bool();
        slots.push(Slot {
            sym,
            kind: SlotKind::Bool,
        });
        Bool::wrap(ctx, term)
    }

    fn lift(leaves: &mut impl Iterator<Item = Lifted>) -> Self::Concrete {
        match leaves.next() {
            Some(Lifted::Bool(b)) => b,
            other => panic!("Bool::lift expected a Boolean leaf, got {other:?}"),
        }
    }
}

macro_rules! tuple_symbolic {
    ($($name:ident),+) => {
        impl<'c, $($name: Symbolic<'c>),+> Symbolic<'c> for ($($name,)+) {
            type Concrete = ($($name::Concrete,)+);

            fn fresh(ctx: &'c Ctx, slots: &mut Vec<Slot>) -> Self {
                ($($name::fresh(ctx, slots),)+)
            }

            fn lift(leaves: &mut impl Iterator<Item = Lifted>) -> Self::Concrete {
                ($($name::lift(leaves),)+)
            }
        }
    };
}

tuple_symbolic!(A);
tuple_symbolic!(A, B);
tuple_symbolic!(A, B, C);

/// The result of a [`Forall::check`].
///
/// `Proved` always carries a [`Certificate`] that was **already re-checked** by
/// the solver before this value was produced ([`prove`]'s contract); call
/// [`Certificate::verify`] to re-run the independent check yourself.
pub enum Outcome<T> {
    /// The property holds for all inputs satisfying the precondition; carries an
    /// independently re-checkable certificate (boxed — the report is large).
    Proved(Box<Certificate>),
    /// The property fails: a concrete input (satisfying the precondition) that
    /// falsifies it, lifted into the user's input type.
    Counterexample(T),
    /// The query was not decided within the configured budgets.
    Unknown(UnknownReason),
}

impl<T> std::fmt::Debug for Outcome<T>
where
    T: std::fmt::Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Outcome::Proved(_) => f.write_str("Proved(<certificate>)"),
            Outcome::Counterexample(t) => write!(f, "Counterexample({t:?})"),
            Outcome::Unknown(r) => write!(f, "Unknown({r:?})"),
        }
    }
}

/// A re-checkable proof that a property holds.
///
/// Wraps the solver's [`EvidenceReport`] (the refutation of `hyps ∧ ¬goal`) plus,
/// when the result is in the reconstructable fragment, a standalone Lean module
/// string. The Lean module is **best-effort** — `None` is honest, never a false
/// promise.
pub struct Certificate {
    /// The underlying self-checking evidence report.
    pub report: EvidenceReport,
    /// A standalone, externally-checkable Lean 4 module, when reconstruction
    /// covered this query's fragment.
    pub lean: Option<String>,
    /// The arena and the full `hyps ∧ ¬goal` query, kept so [`Certificate::verify`]
    /// can re-run the independent check.
    inner: CertInner,
}

struct CertInner {
    ctx_arena: std::cell::RefCell<axeyum_ir::TermArena>,
    query: Vec<TermId>,
}

impl Certificate {
    /// Independently re-validates the proof by re-running the evidence check
    /// against the original `hyps ∧ ¬goal` query.
    ///
    /// # Errors
    ///
    /// Returns [`SolverError`] if the stored certificate fails to re-parse or a
    /// replay hits an internal invariant violation. A clean `Ok(false)` means
    /// the certificate did not hold up (it should never, given `prove` already
    /// re-checked it).
    pub fn verify(&self) -> Result<bool, SolverError> {
        let arena = self.inner.ctx_arena.borrow();
        self.report.evidence.check(&arena, &self.inner.query)
    }

    /// The standalone Lean module proving this refutation, if reconstruction
    /// covered the fragment. Best-effort: `None` for fragments outside the Lean
    /// reconstructor's reach (e.g. most LRA), never a false promise.
    #[must_use]
    pub fn to_lean_module(&self) -> Option<&str> {
        self.lean.as_deref()
    }
}

/// Builder for a property check: resource budgets and whether to attempt a Lean
/// certificate. Construct with [`crate::property`].
#[derive(Debug, Clone, Default)]
pub struct PropertyBuilder {
    config: SolverConfig,
    certificate: bool,
}

impl PropertyBuilder {
    /// A fresh builder with default budgets and no Lean-certificate attempt.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Sets a wall-clock timeout.
    #[must_use]
    pub fn timeout(mut self, timeout: std::time::Duration) -> Self {
        self.config.timeout = Some(timeout);
        self
    }

    /// Sets the translation node budget (admission control for large queries).
    #[must_use]
    pub fn node_budget(mut self, budget: u64) -> Self {
        self.config.node_budget = Some(budget);
        self
    }

    /// Sets the deterministic resource budget (reproducible across machines).
    #[must_use]
    pub fn seed(mut self, resource_limit: u64) -> Self {
        self.config.resource_limit = Some(resource_limit);
        self
    }

    /// When `true`, a `Proved` outcome attempts to also build a standalone Lean
    /// module (best-effort). The in-process certificate is *always* present and
    /// re-checked regardless of this flag.
    #[must_use]
    pub fn certificate(mut self, on: bool) -> Self {
        self.certificate = on;
        self
    }

    /// Declares the universally-quantified symbolic inputs of type `T` and moves
    /// to the [`Forall`] stage. Borrows `ctx` for the lifetime of the inputs.
    #[must_use]
    pub fn forall<'c, T: Symbolic<'c>>(self, ctx: &'c Ctx) -> Forall<'c, T> {
        let mut slots = Vec::new();
        let inputs = T::fresh(ctx, &mut slots);
        Forall {
            ctx,
            inputs,
            slots,
            hypotheses: Vec::new(),
            builder: self,
            _marker: PhantomData,
        }
    }
}

/// The middle stage: symbolic inputs are declared; add a precondition with
/// [`Forall::assuming`], then decide with [`Forall::check`].
pub struct Forall<'c, T: Symbolic<'c>> {
    ctx: &'c Ctx,
    inputs: T,
    slots: Vec<Slot>,
    hypotheses: Vec<TermId>,
    builder: PropertyBuilder,
    _marker: PhantomData<T>,
}

impl<'c, T: Symbolic<'c> + Copy> Forall<'c, T> {
    /// Adds a precondition: the property only needs to hold for inputs satisfying
    /// `pre`. Returns the [`Bool`] term to assume. Can be called multiple times
    /// (the assumptions are conjoined).
    #[must_use]
    pub fn assuming(mut self, pre: impl FnOnce(T) -> Bool<'c>) -> Self {
        let term = pre(self.inputs).term();
        self.hypotheses.push(term);
        self
    }

    /// Decides whether `prop` holds for all inputs satisfying the assumptions.
    ///
    /// # Errors
    ///
    /// Returns [`SolverError`] from the underlying engine (a failed self-check is
    /// a soundness alarm). The verdict itself (`Proved`/`Counterexample`/
    /// `Unknown`) is the `Ok` value, never an error.
    pub fn check(
        self,
        prop: impl FnOnce(T) -> Bool<'c>,
    ) -> Result<Outcome<T::Concrete>, SolverError> {
        let goal = prop(self.inputs).term();
        let hypotheses = self.hypotheses;
        let want_lean = self.builder.certificate;
        let config = self.builder.config;
        let slots = self.slots;

        // The refutation query `hyps ∧ ¬goal`, reconstructed here so the
        // certificate can carry it for an independent re-check. `goal` is a
        // Boolean term, so the negation is well-formed (`build_checked` keeps the
        // unwrap a crate-private internal invariant).
        let query: Vec<TermId> = {
            let neg = self.ctx.build_checked(|a| a.not(goal));
            let mut q = hypotheses.clone();
            q.push(neg);
            q
        };

        // `prove` refutes `hyps ∧ ¬goal`; it borrows the arena mutably.
        let outcome = self
            .ctx
            .with_arena_mut(|arena| prove(arena, &hypotheses, goal, &config))?;

        match outcome {
            ProofOutcome::Proved(report) => {
                let lean = if want_lean {
                    // Best-effort Lean module over the same `hyps ∧ ¬goal` query;
                    // `None` for fragments outside the reconstructor, never a false
                    // promise. The QF_BV reconstructor keys off *separate*
                    // top-level conjuncts (not a single `and`/double-negation), so
                    // we flatten the query into its conjuncts first — semantically
                    // identical, just the shape the reconstructor recognizes.
                    self.ctx.with_arena_mut(|arena| {
                        let flat = flatten_conjuncts(arena, &query);
                        prove_unsat_to_lean_module(arena, &flat)
                            .ok()
                            .map(|(_, module)| module)
                    })
                } else {
                    None
                };
                // Snapshot a fresh arena clone for `verify` against the query.
                let arena_clone = self.ctx.with_arena_mut(|arena| arena.clone());
                Ok(Outcome::Proved(Box::new(Certificate {
                    report: *report,
                    lean,
                    inner: CertInner {
                        ctx_arena: std::cell::RefCell::new(arena_clone),
                        query,
                    },
                })))
            }
            ProofOutcome::Disproved(model) => {
                let mut leaves = slots.iter().map(|slot| lift_slot(&model, *slot));
                let concrete = T::lift(&mut leaves);
                Ok(Outcome::Counterexample(concrete))
            }
            ProofOutcome::Unknown(reason) => Ok(Outcome::Unknown(reason)),
        }
    }
}

/// Splits each assertion into its top-level conjuncts, stripping double
/// negations (`¬¬x → x`), so the result is a flat list whose conjunction is
/// logically equivalent to `assertions`. The `QF_BV` Lean reconstructor keys off
/// separate top-level conjuncts, so this widens the fragment for which a Lean
/// module is emitted without changing the query's meaning.
fn flatten_conjuncts(arena: &TermArena, assertions: &[TermId]) -> Vec<TermId> {
    let mut out = Vec::with_capacity(assertions.len());
    let mut stack: Vec<TermId> = assertions.iter().rev().copied().collect();
    while let Some(t) = stack.pop() {
        match arena.node(t) {
            TermNode::App {
                op: Op::BoolAnd,
                args,
            } => {
                // Push conjuncts (reversed to preserve left-to-right order).
                for &arg in args.iter().rev() {
                    stack.push(arg);
                }
            }
            TermNode::App {
                op: Op::BoolNot,
                args,
            } if args.len() == 1 => {
                // Strip `¬¬x → x`; otherwise keep the negation as a leaf.
                if let TermNode::App {
                    op: Op::BoolNot,
                    args: inner,
                } = arena.node(args[0])
                {
                    if inner.len() == 1 {
                        stack.push(inner[0]);
                        continue;
                    }
                }
                out.push(t);
            }
            _ => out.push(t),
        }
    }
    out
}

/// Lifts one symbol's model value into a [`Lifted`] leaf. A symbol the model did
/// not pin (a don't-care) decodes to a default zero/`false` of the right shape —
/// any concrete value witnesses the counterexample, so a default is sound.
fn lift_slot(model: &axeyum_solver::Model, slot: Slot) -> Lifted {
    let value = model.get(slot.sym);
    match slot.kind {
        SlotKind::Bv => match value.as_ref().and_then(Value::as_bv) {
            Some((width, value)) => Lifted::Bv { width, value },
            // Don't-care: any value satisfies the counterexample; width is
            // recovered from the model when present, else reported as 0.
            None => Lifted::Bv { width: 0, value: 0 },
        },
        SlotKind::Int => Lifted::Int(value.as_ref().and_then(Value::as_int).unwrap_or(0)),
        SlotKind::Bool => Lifted::Bool(value.as_ref().and_then(Value::as_bool).unwrap_or(false)),
    }
}
