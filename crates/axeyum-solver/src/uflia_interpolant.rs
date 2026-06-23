//! Conjunctive Craig interpolation for `QF_UFLIA` (linear integer arithmetic
//! with uninterpreted functions over int/bool sorts).
//!
//! [`uflia_interpolant`] takes two conjunctions of `QF_UFLIA` literals, `A` and
//! `B`, whose conjunction is unsatisfiable, and returns a Craig interpolant `I`
//! (a Boolean [`TermId`]) such that `A ⇒ I`, `I ∧ B ⇒ ⊥`, and every
//! uninterpreted symbol **and function** of `I` is shared by `A` and `B`.
//!
//! ## Construction (Ackermannize → conjunctive LIA interpolant → translate back)
//!
//! 1. **One shared Ackermannization.** A single
//!    [`eliminate_functions`](axeyum_rewrite::eliminate_functions) call over the
//!    combined `A ++ B` abstracts each distinct application `f(args)` to one
//!    fresh integer/bool variable (the internal memo aligns the two partitions —
//!    two separate calls would not). Because `eliminate_functions` declares the
//!    fresh symbol with the function's **result** sort, an `Int`-result UF
//!    abstracts to a fresh `Int` symbol — exactly what `LIA` needs. Its
//!    [`abstraction`](axeyum_rewrite::FunctionElimination::abstraction) is the
//!    rewritten, function-free assertions **without** congruence lemmas — the
//!    relaxation we want — and is 1:1 with the input in input order (verified
//!    below), so the first `|A|` entries are `A'` and the rest are `B'`.
//! 2. **Conjunctive LIA interpolant on the relaxation.**
//!    [`lia_interpolant`](crate::lia_interpolant) on `(A', B')`. Because the
//!    abstraction drops congruence, `A' ∧ B'` is a relaxation of the
//!    Ackermannized formula: if it is unsat the original is unsat, and the LIA
//!    interpolant is over shared integer symbols (including shared fresh
//!    `!fn_app_*` variables). If `A' ∧ B'` is sat — the refutation needed a
//!    congruence lemma the conjunctive method cannot express — or if the integer
//!    unsatisfiability needs cuts the rational relaxation cannot witness,
//!    `lia_interpolant` declines (`Ok(None)` / `Unsupported`) and so do we.
//! 3. **Translate fresh symbols back to applications.** Every fresh symbol in
//!    the LIA interpolant is replaced by its original application term, rebuilt
//!    with [`TermArena::apply`] (recursively for nested applications). A shared
//!    application has shared arguments, so the result is over shared terms.
//!
//! ## Trust
//!
//! The Ackermannization and back-translation are **entirely untrusted**.
//! Soundness comes only from [`verify_uflia_interpolant`], which re-checks all
//! three Craig conditions on the **original** `QF_UFLIA` partitions with
//! [`check_with_uf_arithmetic`] before any interpolant is returned. Any decision
//! that is not the expected `unsat`, any shared-vocabulary violation (over both
//! symbols and function ids), or any construction failure yields `Ok(None)` (a
//! sound decline) — never a wrong interpolant.

use std::collections::{BTreeMap, BTreeSet};

use axeyum_ir::{FuncId, Op, SymbolId, TermArena, TermId, TermNode};
use axeyum_rewrite::eliminate_functions;

use crate::backend::{CheckResult, SolverConfig, SolverError};
use crate::euf::check_with_uf_arithmetic;
use crate::int_reconstruct::{
    reconstruct_diophantine_to_lean_module, reconstruct_int_inequality_to_lean_module,
};
use crate::{ProofFragment, lia_interpolant, prove_lia_unsat_by_diophantine};

/// Computes a conjunctive `QF_UFLIA` Craig interpolant for the partition
/// `(a_assertions, b_assertions)`.
///
/// Returns `Ok(Some(I))` with a fully re-verified interpolant when `A ∧ B` is
/// unsatisfiable through the Ackermannize → `LIA`-interpolant → translate
/// construction; `Ok(None)` when `A ∧ B` is satisfiable, when the refutation
/// needs a congruence lemma the conjunctive method cannot express, when the
/// integer unsatisfiability needs cuts the rational relaxation cannot witness,
/// or when any construction / re-check step fails (a sound decline). An
/// interpolant is **never** returned unverified.
///
/// # Errors
///
/// Returns [`SolverError`] only if the verifying `QF_UFLIA` decider itself
/// errors (a procedure-bug soundness alarm); ordinary unsupported input declines
/// with `Ok(None)`.
pub fn uflia_interpolant(
    arena: &mut TermArena,
    a_assertions: &[TermId],
    b_assertions: &[TermId],
) -> Result<Option<TermId>, SolverError> {
    build_verified_uflia_interpolant(arena, a_assertions, b_assertions)
}

/// Builds the verified conjunctive `QF_UFLIA` interpolant `I` for `A ∧ B` (or
/// `None`). This is the single source of truth for `I`; [`uflia_interpolant`]
/// forwards to it directly and [`uflia_interpolant_certified`] reuses it, so the
/// returned `I` is byte-identical across both entry points.
fn build_verified_uflia_interpolant(
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

    // (2) Conjunctive LIA interpolant on the function-free relaxation. A SAT
    // relaxation (congruence was needed), a cuts-needed integer refutation the
    // rational relaxation cannot witness, an LIA `Unsupported` shape after
    // abstraction, or a self-check decline all collapse to a sound `Ok(None)`.
    let lia_interp = match lia_interpolant(arena, &a_prime, &b_prime) {
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
    let Some(interp) = translator.translate_term(arena, lia_interp) else {
        return Ok(None);
    };
    if translator.declined {
        return Ok(None);
    }

    // (4) The soundness anchor: re-check the three Craig conditions on the
    // ORIGINAL UFLIA partitions with the translated interpolant.
    if verify_uflia_interpolant(arena, a_assertions, b_assertions, interp)? {
        Ok(Some(interp))
    } else {
        Ok(None)
    }
}

/// Re-checks the three Craig conditions for `interp` against the original
/// `QF_UFLIA` partitions with [`check_with_uf_arithmetic`]:
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
/// Propagates a [`SolverError`] from the `QF_UFLIA` decider (a soundness alarm),
/// never an ordinary decline.
pub fn verify_uflia_interpolant(
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

/// A **certified** conjunctive `QF_UFLIA` Craig interpolant: the interpolant `I` for an
/// unsatisfiable integer `A ∧ B`, paired with two externally-checkable, **kernel-checked**
/// integer refutations witnessing its two soundness conditions.
///
/// - [`a_certificate`](Self::a_certificate) is a self-contained Lean 4 module
///   (`prelude`-mode source) re-proving `A ∧ ¬I ⊢ ⊥` over the integer prelude (Craig
///   condition 1, `A ⇒ I`);
/// - [`b_certificate`](Self::b_certificate) is the same for `I ∧ B ⊢ ⊥` (Craig
///   condition 2).
///
/// `I` is a single linear-integer comparison whose only uninterpreted-function
/// applications are **opaque** shared integers (the conjunctive `QF_UFLIA` construction
/// declines whenever a refutation would need functional consistency / congruence — the
/// function-free relaxation is then `sat` — so the certifiable interpolant is always
/// congruence-free). Each of `A ∧ ¬I` and `I ∧ B` is therefore an integer **conjunction**
/// over opaque applications, reconstructed through one of the integer-prelude shapes the
/// `int_reconstruct` module covers ([`ProofFragment::Diophantine`] or
/// [`ProofFragment::IntInequality`]) — where each maximal non-arithmetic subterm `(f c)`
/// is treated as a fresh opaque integer (`AtomVar::Opaque`, sound because an `(f c)` is
/// some integer, so the free-variable system is a generalization).
///
/// Both modules are produced by [`crate::prove_unsat_to_lean_module`], which
/// **kernel-checks** the refutation in-tree (`infer` + `def_eq False`, no `sorryAx`)
/// before rendering; an independent `lean` binary re-checks the same module. Carcara has
/// **no** integer `lia_generic` rule (it warns and marks the proof `holey`), so for
/// integers the external checker is the **Lean kernel**, not Carcara.
///
/// # Boundary — covered shapes only
///
/// The certifiable interpolant `I` is a single integer linear comparison, so `¬I` is one
/// (dual) comparison and both `A ∧ ¬I` and `I ∧ B` are integer conjunctions over opaque
/// applications. They are certified here **only** when each reconstructs through a covered
/// integer-prelude fragment. A `QF_UFLIA` interpolant whose `A ∧ ¬I` or `I ∧ B` needs an
/// **uncovered** integer refutation (a general cut, or a multivariate rational-relaxation
/// refutation the integer reconstructor declines) is **not** certified here and stays
/// `Validated`. This is an honest boundary — not all `QF_UFLIA` interpolants are
/// certified, only those whose two soundness conjunctions land in the covered integer
/// shapes.
#[derive(Debug, Clone)]
pub struct UfliaInterpolantCertificate {
    /// The verified interpolant term `I` (byte-identical to what [`uflia_interpolant`]
    /// returns for the same `(A, B)`).
    pub interpolant: TermId,
    /// `A ∧ ¬I`, the conjunction the [`a_certificate`](Self::a_certificate) refutes.
    pub a_and_not_i: Vec<TermId>,
    /// `I ∧ B`, the conjunction the [`b_certificate`](Self::b_certificate) refutes.
    pub i_and_b: Vec<TermId>,
    /// Kernel-checked Lean module re-proving `A ∧ ¬I ⊢ ⊥` (Craig condition 1).
    pub a_certificate: String,
    /// Kernel-checked Lean module re-proving `I ∧ B ⊢ ⊥` (Craig condition 2).
    pub b_certificate: String,
    /// The integer-prelude fragment of [`a_certificate`](Self::a_certificate)
    /// (one of [`ProofFragment::Diophantine`] / [`ProofFragment::IntInequality`]).
    pub a_fragment: ProofFragment,
    /// The integer-prelude fragment of [`b_certificate`](Self::b_certificate).
    pub b_fragment: ProofFragment,
}

/// Produces a **certified** Craig interpolant for the unsatisfiable conjunctive
/// `QF_UFLIA` partition `A = a_assertions`, `B = b_assertions`: the same verified
/// interpolant [`uflia_interpolant`] returns, **plus** two kernel-checked integer
/// certificates — Lean modules re-proving `A ∧ ¬I` and `I ∧ B` over the integer prelude
/// (treating every uninterpreted-function application as an opaque integer) — that an
/// independent `lean` binary can accept on its own.
///
/// This is the `Checked`-assurance upgrade of the `Validated` [`uflia_interpolant`]: the
/// interpolant was already verify-before-return over the original `QF_UFLIA` partitions;
/// here we additionally emit a kernel-checked integer certificate for each of its two
/// soundness conditions, and return it **only** when both conjunctions reconstruct through
/// a covered integer-prelude fragment ([`ProofFragment::Diophantine`] or
/// [`ProofFragment::IntInequality`]). `¬I` is built as the explicit **dual** comparison
/// (`¬(e ≤ 0) = e > 0`, `¬(e < 0) = e ≥ 0`) rather than a `not`-wrapper, so the integer
/// fragment classifier — which reads bare comparisons, not `not` — covers it.
///
/// # Boundary
///
/// Only the covered integer shapes are certified (see [`UfliaInterpolantCertificate`]).
/// This function declines (`Ok(None)`) whenever [`uflia_interpolant`] declines, whenever
/// `¬I` cannot be built as a bare dual comparison (e.g. an equality interpolant, whose
/// negation is a disjunction), or whenever either conjunction does **not** reconstruct
/// through a covered integer fragment. A caller that gets `Ok(None)` should fall back to
/// the `Validated` [`uflia_interpolant`] path — this function NEVER returns an uncertified
/// interpolant dressed as certified.
///
/// # Errors
///
/// Propagates [`SolverError`] from the shared verifying `QF_UFLIA` decider (a procedure-bug
/// soundness alarm); ordinary unsupported input declines with `Ok(None)`.
pub fn uflia_interpolant_certified(
    arena: &mut TermArena,
    a_assertions: &[TermId],
    b_assertions: &[TermId],
) -> Result<Option<UfliaInterpolantCertificate>, SolverError> {
    // 1. The verified interpolant `I` (identical to `uflia_interpolant`'s output).
    let Some(interpolant) = build_verified_uflia_interpolant(arena, a_assertions, b_assertions)?
    else {
        return Ok(None);
    };

    // 2. Form the two Craig-condition conjunctions. `¬I` is the explicit dual comparison
    //    (a bare integer comparison the integer fragment classifier reads), not a
    //    `not`-wrapper.
    let Some(not_interpolant) = dual_int_comparison(arena, interpolant) else {
        return Ok(None);
    };
    let mut a_and_not_i: Vec<TermId> = a_assertions.to_vec();
    a_and_not_i.push(not_interpolant);
    let mut i_and_b: Vec<TermId> = Vec::with_capacity(b_assertions.len() + 1);
    i_and_b.push(interpolant);
    i_and_b.extend_from_slice(b_assertions);

    // 3. Reconstruct EACH conjunction to a kernel-checked integer Lean module, requiring a
    //    COVERED integer fragment; either failing ⇒ decline to the `Validated` path (never
    //    an uncertified interpolant dressed as certified).
    let Some((a_fragment, a_certificate)) = integer_certificate(arena, &a_and_not_i) else {
        return Ok(None);
    };
    let Some((b_fragment, b_certificate)) = integer_certificate(arena, &i_and_b) else {
        return Ok(None);
    };

    Ok(Some(UfliaInterpolantCertificate {
        interpolant,
        a_and_not_i,
        i_and_b,
        a_certificate,
        b_certificate,
        a_fragment,
        b_fragment,
    }))
}

/// Reconstructs the integer conjunction `assertions` (over opaque applications) to a
/// kernel-checked Lean module, returning `Some((fragment, module))` **only** when it
/// reconstructs through a COVERED integer-prelude fragment ([`ProofFragment::Diophantine`]
/// or [`ProofFragment::IntInequality`]) and the rendered module carries no `sorryAx`.
///
/// Unlike the `QF_LIA` certified path, this **bypasses** the general
/// [`crate::scan_proof_fragment`] router: that router classifies any term carrying an
/// uninterpreted-function application as `QF_UF` (`has_func` takes precedence over
/// arithmetic), which would route these integer conjunctions to the EUF reconstructor (it
/// declines — they are not pure-EUF). Since the conjunctive `QF_UFLIA` construction
/// guarantees both conjunctions are integer refutations over **opaque** applications (the
/// interpolant is congruence-free), we invoke the integer-prelude reconstructors directly —
/// the Diophantine equality reconstructor first (it owns `gcd`-infeasible equality systems),
/// then the integer-inequality interval reconstructor. Each treats every maximal
/// non-arithmetic subterm `(f c)` as a fresh opaque integer (sound: an `(f c)` is some
/// integer, so the free-variable system is a generalization). Both reconstructors gate the
/// `False` proof through their own integer-prelude kernel (`infer` + `def_eq False`) before
/// rendering, so a returned module is already kernel-accepted.
///
/// Any reconstruction failure, or a module that somehow carries `sorryAx`, returns `None`
/// so the certified path declines to `Validated` — never an uncertified interpolant dressed
/// as certified.
fn integer_certificate(
    arena: &TermArena,
    assertions: &[TermId],
) -> Option<(ProofFragment, String)> {
    // Diophantine equality system first (matches the `scan_proof_fragment` priority), then
    // the single-variable integer-interval cut. Both build their own integer-prelude kernel
    // and gate `infer` + `def_eq False` before rendering.
    let (fragment, module) = if prove_lia_unsat_by_diophantine(arena, assertions) {
        (
            ProofFragment::Diophantine,
            reconstruct_diophantine_to_lean_module(arena, assertions).ok()?,
        )
    } else {
        (
            ProofFragment::IntInequality,
            reconstruct_int_inequality_to_lean_module(arena, assertions).ok()?,
        )
    };
    // Defensive: a covered integer module is kernel-checked and never leans on the `sorryAx`
    // escape hatch; refuse to certify if it somehow does.
    if module.contains("sorryAx") {
        return None;
    }
    Some((fragment, module))
}

/// Builds the explicit dual (logical negation) of the interpolant comparison `I` as a
/// single **bare** integer comparison term, so the integer fragment classifier — which
/// reads bare comparisons, not a `not`-wrapper — can route it.
///
/// `I` is produced by [`build_verified_uflia_interpolant`] (via the underlying
/// `lia_interpolant`) as `int_le(e, 0)`, `int_lt(e, 0)`, or `eq(e, 0)`. The duals of the
/// inequalities are `int_gt(e, 0)` and `int_ge(e, 0)`. An equality interpolant `e = 0`
/// has no single-comparison dual (`¬(e = 0)` is a disjunction `e < 0 ∨ e > 0`), so it
/// returns `None` ⇒ decline (such an interpolant stays `Validated`).
fn dual_int_comparison(arena: &mut TermArena, interpolant: TermId) -> Option<TermId> {
    let (op, lhs, rhs) = match arena.node(interpolant) {
        TermNode::App { op, args } if args.len() == 2 => (*op, args[0], args[1]),
        _ => return None,
    };
    match op {
        Op::IntLe => arena.int_gt(lhs, rhs).ok(),
        Op::IntLt => arena.int_ge(lhs, rhs).ok(),
        _ => None,
    }
}

/// Rebuilds an LIA interpolant term, substituting each fresh Ackermann symbol
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
/// operator. Only the operators an `LIA` interpolant can contain (integer
/// arithmetic, integer relations, equality, Boolean structure, and
/// uninterpreted applications) are handled; anything else declines (`None`).
fn rebuild_app(arena: &mut TermArena, op: Op, args: &[TermId]) -> Option<TermId> {
    let r = match (op, args) {
        (Op::Apply(func), _) => arena.apply(func, args),
        (Op::BoolNot, [a]) => arena.not(*a),
        (Op::BoolAnd, [a, b]) => arena.and(*a, *b),
        (Op::BoolOr, [a, b]) => arena.or(*a, *b),
        (Op::Eq, [a, b]) => arena.eq(*a, *b),
        (Op::IntNeg, [a]) => arena.int_neg(*a),
        (Op::IntAdd, [a, b]) => arena.int_add(*a, *b),
        (Op::IntSub, [a, b]) => arena.int_sub(*a, *b),
        (Op::IntMul, [a, b]) => arena.int_mul(*a, *b),
        (Op::IntLt, [a, b]) => arena.int_lt(*a, *b),
        (Op::IntLe, [a, b]) => arena.int_le(*a, *b),
        (Op::IntGt, [a, b]) => arena.int_gt(*a, *b),
        (Op::IntGe, [a, b]) => arena.int_ge(*a, *b),
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
