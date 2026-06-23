//! Conjunctive Craig interpolation for `QF_UFLRA` (linear real arithmetic with
//! uninterpreted functions over real/bool sorts).
//!
//! [`uflra_interpolant`] takes two conjunctions of `QF_UFLRA` literals, `A` and
//! `B`, whose conjunction is unsatisfiable, and returns a Craig interpolant `I`
//! (a Boolean [`TermId`]) such that `A ⇒ I`, `I ∧ B ⇒ ⊥`, and every
//! uninterpreted symbol **and function** of `I` is shared by `A` and `B`.
//!
//! ## Construction (Ackermannize → conjunctive LRA interpolant → translate back)
//!
//! 1. **One shared Ackermannization.** A single
//!    [`eliminate_functions`](axeyum_rewrite::eliminate_functions) call over the
//!    combined `A ++ B` abstracts each distinct application `f(args)` to one
//!    fresh real/bool variable (the internal memo aligns the two partitions —
//!    two separate calls would not). Its
//!    [`abstraction`](axeyum_rewrite::FunctionElimination::abstraction) is the
//!    rewritten, function-free assertions **without** congruence lemmas — the
//!    relaxation we want — and is 1:1 with the input in input order (verified
//!    below), so the first `|A|` entries are `A'` and the rest are `B'`.
//! 2. **Conjunctive LRA interpolant on the relaxation.**
//!    [`lra_interpolant`](crate::lra_interpolant) on `(A', B')`. Because the
//!    abstraction drops congruence, `A' ∧ B'` is a relaxation of the
//!    Ackermannized formula: if it is unsat the original is unsat, and the LRA
//!    interpolant is over shared real symbols (including shared fresh
//!    `!fn_app_*` variables). If `A' ∧ B'` is sat — the refutation needed a
//!    congruence lemma the conjunctive method cannot express — `lra_interpolant`
//!    declines (`Ok(None)`) and so do we.
//! 3. **Translate fresh symbols back to applications.** Every fresh symbol in
//!    the LRA interpolant is replaced by its original application term, rebuilt
//!    with [`TermArena::apply`] (recursively for nested applications). A shared
//!    application has shared arguments, so the result is over shared terms.
//!
//! ## Trust
//!
//! The Ackermannization and back-translation are **entirely untrusted**.
//! Soundness comes only from [`verify_uflra_interpolant`], which re-checks all
//! three Craig conditions on the **original** `QF_UFLRA` partitions with
//! [`check_with_uf_arithmetic`] before any interpolant is returned. Any decision
//! that is not the expected `unsat`, any shared-vocabulary violation (over both
//! symbols and function ids), or any construction failure yields `Ok(None)` (a
//! sound decline) — never a wrong interpolant.

use std::collections::{BTreeMap, BTreeSet};

use axeyum_cnf::AletheCommand;
use axeyum_ir::{FuncId, Op, SymbolId, TermArena, TermId, TermNode};
use axeyum_rewrite::eliminate_functions;

use crate::backend::{CheckResult, SolverConfig, SolverError};
use crate::euf::check_with_uf_arithmetic;
use crate::{lra_interpolant, prove_uflra_unsat_alethe};

/// Computes a conjunctive `QF_UFLRA` Craig interpolant for the partition
/// `(a_assertions, b_assertions)`.
///
/// Returns `Ok(Some(I))` with a fully re-verified interpolant when `A ∧ B` is
/// unsatisfiable through the Ackermannize → LRA-interpolant → translate
/// construction; `Ok(None)` when `A ∧ B` is satisfiable, when the refutation
/// needs a congruence lemma the conjunctive method cannot express, or when any
/// construction / re-check step fails (a sound decline). An interpolant is
/// **never** returned unverified.
///
/// # Errors
///
/// Returns [`SolverError`] only if the verifying `QF_UFLRA` decider itself
/// errors (a procedure-bug soundness alarm); ordinary unsupported input declines
/// with `Ok(None)`.
pub fn uflra_interpolant(
    arena: &mut TermArena,
    a_assertions: &[TermId],
    b_assertions: &[TermId],
) -> Result<Option<TermId>, SolverError> {
    build_verified_uflra_interpolant(arena, a_assertions, b_assertions)
}

/// Builds the verified conjunctive `QF_UFLRA` interpolant `I` for `A ∧ B` (or
/// `None`). This is the single source of truth for `I`; [`uflra_interpolant`]
/// forwards to it directly and [`uflra_interpolant_certified`] reuses it, so the
/// returned `I` is byte-identical across both entry points.
fn build_verified_uflra_interpolant(
    arena: &mut TermArena,
    a_assertions: &[TermId],
    b_assertions: &[TermId],
) -> Result<Option<TermId>, SolverError> {
    // (1) One shared Ackermannization over the combined partitions.
    let mut combined: Vec<TermId> = Vec::with_capacity(a_assertions.len() + b_assertions.len());
    combined.extend_from_slice(a_assertions);
    combined.extend_from_slice(b_assertions);

    // An unsupported construct in Ackermannization is a clean decline.
    let Ok(elimination) = eliminate_functions(arena, &combined) else {
        return Ok(None);
    };

    let abstraction = elimination.abstraction();
    // The abstraction must be 1:1 with the input, in input order, so the A/B
    // split is sound. (Confirmed against `crates/axeyum-rewrite/src/functions.rs`:
    // `abstraction` is `rewritten.clone()`, one rewritten entry per input
    // assertion in order.) Defensively re-check the length here; if it does not
    // hold, decline rather than risk a misaligned split.
    if abstraction.len() != combined.len() {
        return Ok(None);
    }
    let (a_prime, b_prime) = abstraction.split_at(a_assertions.len());
    let a_prime = a_prime.to_vec();
    let b_prime = b_prime.to_vec();

    // Snapshot the application map (the arg slices borrow `arena`) before any
    // further `arena` mutation.
    let applications: Vec<(FuncId, Vec<TermId>, SymbolId)> = elimination
        .applications()
        .into_iter()
        .map(|(func, args, fresh)| (func, args.to_vec(), fresh))
        .collect();

    // (2) Conjunctive LRA interpolant on the function-free relaxation. A SAT
    // relaxation (congruence was needed), an LRA `Unsupported` shape after
    // abstraction (e.g. a real disequality the conjunctive method cannot handle),
    // or a self-check decline all collapse to a sound `Ok(None)`.
    let lra_interp = match lra_interpolant(arena, &a_prime, &b_prime) {
        Ok(Some(interp)) => interp,
        Ok(None) | Err(SolverError::Unsupported(_)) => return Ok(None),
        Err(other) => return Err(other),
    };

    // (3) Translate fresh Ackermann symbols in the interpolant back to UF terms.
    let fresh_to_app: BTreeMap<SymbolId, (FuncId, Vec<TermId>)> = applications
        .iter()
        .map(|(func, args, fresh)| (*fresh, (*func, args.clone())))
        .collect();
    let mut translator = Translator {
        fresh_to_app,
        term_memo: BTreeMap::new(),
        symbol_memo: BTreeMap::new(),
        declined: false,
    };
    let Some(interp) = translator.translate_term(arena, lra_interp) else {
        return Ok(None);
    };
    if translator.declined {
        return Ok(None);
    }

    // (4) The soundness anchor: re-check the three Craig conditions on the
    // ORIGINAL UFLRA partitions with the translated interpolant.
    if verify_uflra_interpolant(arena, a_assertions, b_assertions, interp)? {
        Ok(Some(interp))
    } else {
        Ok(None)
    }
}

/// Re-checks the three Craig conditions for `interp` against the original
/// `QF_UFLRA` partitions with [`check_with_uf_arithmetic`]:
///
/// 1. `A ∧ ¬I` is `unsat` (i.e. `A ⇒ I`),
/// 2. `I ∧ B` is `unsat` (i.e. `I ∧ B ⇒ ⊥`),
/// 3. every uninterpreted symbol AND function id of `I` occurs in both `A` and
///    `B`.
///
/// Returns `Ok(true)` only when all three hold; any other decision, vocabulary
/// failure, or builder error yields `Ok(false)`.
///
/// # Errors
///
/// Propagates a [`SolverError`] from the `QF_UFLRA` decider (a soundness alarm),
/// never an ordinary decline.
pub fn verify_uflra_interpolant(
    arena: &mut TermArena,
    a_assertions: &[TermId],
    b_assertions: &[TermId],
    interp: TermId,
) -> Result<bool, SolverError> {
    // (3) Vocabulary over both symbols and function ids.
    let (a_syms, a_funcs) = partition_vocabulary(arena, a_assertions);
    let (b_syms, b_funcs) = partition_vocabulary(arena, b_assertions);
    let (i_syms, i_funcs) = term_vocabulary(arena, interp);
    if !i_syms
        .iter()
        .all(|s| a_syms.contains(s) && b_syms.contains(s))
    {
        return Ok(false);
    }
    if !i_funcs
        .iter()
        .all(|f| a_funcs.contains(f) && b_funcs.contains(f))
    {
        return Ok(false);
    }

    let config = SolverConfig::default();

    // (1) A ∧ ¬I unsat.
    let Ok(not_i) = arena.not(interp) else {
        return Ok(false);
    };
    let mut a_check: Vec<TermId> = a_assertions.to_vec();
    a_check.push(not_i);
    if !matches!(
        check_with_uf_arithmetic(arena, &a_check, &config)?,
        CheckResult::Unsat
    ) {
        return Ok(false);
    }

    // (2) I ∧ B unsat.
    let mut b_check: Vec<TermId> = Vec::with_capacity(b_assertions.len() + 1);
    b_check.push(interp);
    b_check.extend_from_slice(b_assertions);
    if !matches!(
        check_with_uf_arithmetic(arena, &b_check, &config)?,
        CheckResult::Unsat
    ) {
        return Ok(false);
    }

    Ok(true)
}

/// A **certified** conjunctive `QF_UFLRA` Craig interpolant: the interpolant `I`
/// for an unsatisfiable `A ∧ B`, paired with two externally-checkable refutations
/// witnessing its two soundness conditions.
///
/// - [`a_refutation`](Self::a_refutation) is an Alethe `la_generic` proof of
///   `A ∧ ¬I ⊢ ⊥` (Craig condition 1, `A ⇒ I`);
/// - [`b_refutation`](Self::b_refutation) is an Alethe `la_generic` proof of
///   `I ∧ B ⊢ ⊥` (Craig condition 2).
///
/// `I` is a single linear-real comparison whose only uninterpreted-function
/// applications are **opaque** shared reals (the conjunctive `QF_UFLRA`
/// construction declines whenever a refutation would need functional
/// consistency / congruence, so the certifiable interpolant is always
/// congruence-free). Each of `A ∧ ¬I` and `I ∧ B` is therefore a conjunction of
/// linear-real comparisons over opaque applications — refutable by a single
/// `la_generic` step treating every `(f args)` as an opaque real (see
/// [`crate::prove_uflra_unsat_alethe`]).
///
/// Both proofs are self-validated through [`crate::check_alethe_lra`] before this
/// struct is constructed, and each is **independently** checkable by an external
/// checker — Carcara (`la_generic`, accepted when `valid && !holey`, over the
/// **inlined** `.smt2` problem so the `(f args)` atoms render verbatim) or the Lean
/// kernel.
#[derive(Debug, Clone)]
pub struct UflraInterpolantCertificate {
    /// The verified interpolant term `I` (byte-identical to what
    /// [`uflra_interpolant`] returns for the same `(A, B)`).
    pub interpolant: TermId,
    /// `A ∧ ¬I`, the conjunction the [`a_refutation`](Self::a_refutation) refutes.
    pub a_and_not_i: Vec<TermId>,
    /// `I ∧ B`, the conjunction the [`b_refutation`](Self::b_refutation) refutes.
    pub i_and_b: Vec<TermId>,
    /// Alethe `la_generic` (opaque-application) refutation of `A ∧ ¬I`.
    pub a_refutation: Vec<AletheCommand>,
    /// Alethe `la_generic` (opaque-application) refutation of `I ∧ B`.
    pub b_refutation: Vec<AletheCommand>,
}

/// Produces a **certified** Craig interpolant for the unsatisfiable conjunctive
/// `QF_UFLRA` partition `A = a_assertions`, `B = b_assertions`: the same verified
/// interpolant [`uflra_interpolant`] returns, **plus** two `la_generic` refutations
/// — of `A ∧ ¬I` and `I ∧ B`, treating every uninterpreted-function application as
/// an opaque real — that an independent checker (Carcara) can accept on its own.
///
/// This is the `Checked`-assurance upgrade of the `Validated` [`uflra_interpolant`]:
/// the interpolant was already verify-before-return; here we additionally emit an
/// externally-checkable certificate for each of its two soundness conditions, and
/// return it **only** when both refutations are produced and self-check (through
/// [`crate::check_alethe_lra`], whose `la_generic` validation treats `(f args)` as
/// an opaque real). `¬I` is built as the explicit DUAL comparison (`¬(e ≤ 0) = e >
/// 0`, `¬(e < 0) = e ≥ 0`) rather than a `not`-wrapper, so the bare-comparison
/// refutation emitter covers it.
///
/// # Boundary
///
/// Only the CONJUNCTIVE, **congruence-free** `QF_UFLRA` slice is certified here. The
/// conjunctive interpolant construction already declines whenever the refutation
/// needs functional consistency / congruence (the function-free relaxation is then
/// `sat`), so the certifiable interpolant is always over opaque applications and
/// both `A ∧ ¬I` and `I ∧ B` are single-`la_generic` refutable. This function
/// declines (`Ok(None)`) whenever [`uflra_interpolant`] declines, or whenever either
/// refutation cannot be emitted/validated for the produced conjunction (e.g. a shape
/// the opaque emitter cannot reduce). A caller that gets `Ok(None)` should fall back
/// to the `Validated` [`uflra_interpolant`] path — this function NEVER returns an
/// uncertified interpolant dressed as certified.
///
/// # Errors
///
/// Propagates [`SolverError`] from the underlying verifying `QF_UFLRA` decider (a
/// procedure-bug soundness alarm); ordinary unsupported input declines with
/// `Ok(None)`.
pub fn uflra_interpolant_certified(
    arena: &mut TermArena,
    a_assertions: &[TermId],
    b_assertions: &[TermId],
) -> Result<Option<UflraInterpolantCertificate>, SolverError> {
    // 1. The verified interpolant `I` (identical to `uflra_interpolant`'s output).
    let Some(interpolant) = build_verified_uflra_interpolant(arena, a_assertions, b_assertions)?
    else {
        return Ok(None);
    };

    // 2. Form the two Craig-condition conjunctions. `¬I` is the explicit dual
    //    comparison (a bare comparison the opaque emitter lowers), not a
    //    `not`-wrapper.
    let Some(not_interpolant) = dual_comparison(arena, interpolant) else {
        return Ok(None);
    };
    let mut a_and_not_i: Vec<TermId> = a_assertions.to_vec();
    a_and_not_i.push(not_interpolant);
    let mut i_and_b: Vec<TermId> = Vec::with_capacity(b_assertions.len() + 1);
    i_and_b.push(interpolant);
    i_and_b.extend_from_slice(b_assertions);

    // 3. Emit a self-validated opaque-application `la_generic` refutation for each.
    //    Either failing ⇒ decline to the `Validated` path (never an uncertified
    //    interpolant).
    let Some(a_refutation) = prove_uflra_unsat_alethe(arena, &a_and_not_i) else {
        return Ok(None);
    };
    let Some(b_refutation) = prove_uflra_unsat_alethe(arena, &i_and_b) else {
        return Ok(None);
    };

    Ok(Some(UflraInterpolantCertificate {
        interpolant,
        a_and_not_i,
        i_and_b,
        a_refutation,
        b_refutation,
    }))
}

/// Builds the explicit dual (logical negation) of the interpolant comparison `I`
/// as a single bare comparison term, so the bare-comparison refutation emitter can
/// lower it. `I` is produced by [`build_verified_uflra_interpolant`] as exactly
/// `real_le(e, 0)` or `real_lt(e, 0)` (via the underlying `lra_interpolant`), whose
/// duals are `real_gt(e, 0)` and `real_ge(e, 0)`. Any other shape returns `None` ⇒
/// decline.
fn dual_comparison(arena: &mut TermArena, interpolant: TermId) -> Option<TermId> {
    let (op, lhs, rhs) = match arena.node(interpolant) {
        TermNode::App { op, args } if args.len() == 2 => (*op, args[0], args[1]),
        _ => return None,
    };
    match op {
        Op::RealLe => arena.real_gt(lhs, rhs).ok(),
        Op::RealLt => arena.real_ge(lhs, rhs).ok(),
        _ => None,
    }
}

/// Rebuilds an LRA interpolant term, substituting each fresh Ackermann symbol
/// leaf with its original application term.
struct Translator {
    /// `fresh symbol -> (function, rewritten args)`.
    fresh_to_app: BTreeMap<SymbolId, (FuncId, Vec<TermId>)>,
    /// Memo of translated terms (rebuilt structure).
    term_memo: BTreeMap<TermId, TermId>,
    /// Memo of translated application symbols (their reconstructed apply terms).
    symbol_memo: BTreeMap<SymbolId, TermId>,
    /// Set when a fresh symbol or builder step could not be translated; the
    /// caller maps this to a sound decline.
    declined: bool,
}

impl Translator {
    /// Rebuilds `term`, replacing fresh-application symbol leaves by their
    /// reconstructed application terms. `None` on a builder failure.
    fn translate_term(&mut self, arena: &mut TermArena, term: TermId) -> Option<TermId> {
        if let Some(&cached) = self.term_memo.get(&term) {
            return Some(cached);
        }
        let result = match arena.node(term).clone() {
            TermNode::Symbol(symbol) => {
                if self.fresh_to_app.contains_key(&symbol) {
                    self.translate_symbol(arena, symbol)?
                } else {
                    term
                }
            }
            TermNode::BoolConst(_)
            | TermNode::BvConst { .. }
            | TermNode::WideBvConst(_)
            | TermNode::IntConst(_)
            | TermNode::RealConst(_) => term,
            TermNode::App { op, args } => {
                let mut new_args = Vec::with_capacity(args.len());
                for &arg in &args {
                    new_args.push(self.translate_term(arena, arg)?);
                }
                rebuild_app(arena, op, &new_args)?
            }
        };
        self.term_memo.insert(term, result);
        Some(result)
    }

    /// Reconstructs the application term for a fresh Ackermann symbol:
    /// `apply(func, translate(args))`. Arguments that are themselves fresh
    /// symbols are translated recursively. `None` if `symbol` has no application
    /// entry (sets `declined`) or a builder fails.
    fn translate_symbol(&mut self, arena: &mut TermArena, symbol: SymbolId) -> Option<TermId> {
        if let Some(&cached) = self.symbol_memo.get(&symbol) {
            return Some(cached);
        }
        let Some((func, args)) = self.fresh_to_app.get(&symbol).cloned() else {
            // A fresh symbol in the interpolant without an application entry: the
            // construction cannot soundly translate it. Decline.
            self.declined = true;
            return None;
        };
        let mut translated_args = Vec::with_capacity(args.len());
        for arg in args {
            let translated = match arena.node(arg) {
                TermNode::Symbol(inner) if self.fresh_to_app.contains_key(inner) => {
                    let inner = *inner;
                    self.translate_symbol(arena, inner)?
                }
                _ => arg,
            };
            translated_args.push(translated);
        }
        let app = arena.apply(func, &translated_args).ok()?;
        self.symbol_memo.insert(symbol, app);
        Some(app)
    }
}

/// Rebuilds an application node from translated arguments, dispatching on the
/// operator. Only the operators an LRA interpolant can contain (real arithmetic,
/// real relations, equality, Boolean structure, and uninterpreted applications)
/// are handled; anything else declines (`None`).
fn rebuild_app(arena: &mut TermArena, op: Op, args: &[TermId]) -> Option<TermId> {
    let r = match (op, args) {
        (Op::Apply(func), _) => arena.apply(func, args),
        (Op::BoolNot, [a]) => arena.not(*a),
        (Op::BoolAnd, [a, b]) => arena.and(*a, *b),
        (Op::BoolOr, [a, b]) => arena.or(*a, *b),
        (Op::Eq, [a, b]) => arena.eq(*a, *b),
        (Op::RealNeg, [a]) => arena.real_neg(*a),
        (Op::RealAdd, [a, b]) => arena.real_add(*a, *b),
        (Op::RealSub, [a, b]) => arena.real_sub(*a, *b),
        (Op::RealMul, [a, b]) => arena.real_mul(*a, *b),
        (Op::RealLt, [a, b]) => arena.real_lt(*a, *b),
        (Op::RealLe, [a, b]) => arena.real_le(*a, *b),
        (Op::RealGt, [a, b]) => arena.real_gt(*a, *b),
        (Op::RealGe, [a, b]) => arena.real_ge(*a, *b),
        _ => return None,
    };
    r.ok()
}

/// The uninterpreted symbols and function ids appearing in a slice of
/// assertions.
fn partition_vocabulary(
    arena: &TermArena,
    assertions: &[TermId],
) -> (BTreeSet<SymbolId>, BTreeSet<FuncId>) {
    let mut syms = BTreeSet::new();
    let mut funcs = BTreeSet::new();
    for &assertion in assertions {
        collect_vocabulary(arena, assertion, &mut syms, &mut funcs);
    }
    (syms, funcs)
}

/// The uninterpreted symbols and function ids appearing in a single term.
fn term_vocabulary(arena: &TermArena, term: TermId) -> (BTreeSet<SymbolId>, BTreeSet<FuncId>) {
    let mut syms = BTreeSet::new();
    let mut funcs = BTreeSet::new();
    collect_vocabulary(arena, term, &mut syms, &mut funcs);
    (syms, funcs)
}

fn collect_vocabulary(
    arena: &TermArena,
    term: TermId,
    syms: &mut BTreeSet<SymbolId>,
    funcs: &mut BTreeSet<FuncId>,
) {
    let mut stack = vec![term];
    let mut seen = BTreeSet::new();
    while let Some(t) = stack.pop() {
        if !seen.insert(t) {
            continue;
        }
        match arena.node(t) {
            TermNode::Symbol(symbol) => {
                syms.insert(*symbol);
            }
            TermNode::App { op, args } => {
                if let Op::Apply(func) = op {
                    funcs.insert(*func);
                }
                stack.extend(args.iter().copied());
            }
            TermNode::BoolConst(_)
            | TermNode::BvConst { .. }
            | TermNode::WideBvConst(_)
            | TermNode::IntConst(_)
            | TermNode::RealConst(_) => {}
        }
    }
}
