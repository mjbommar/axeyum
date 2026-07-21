//! The verifier: lower a [`Program`], ask the solver whether any panic-class
//! bad state is reachable, and report a verdict.
//!
//! A bug is reachable iff `OR(bad_states)` is satisfiable. We pose this to
//! [`axeyum_solver::prove`] as: prove the goal `¬OR(bad_states)`. An `unsat`
//! refutation of `OR(bad_states)` is a **bounded-safety proof** carrying a
//! re-checked certificate; a `sat` model is a concrete **bug witness**, lifted
//! into typed inputs; `unknown` is surfaced honestly.

use axeyum_ir::{Op, TermArena, TermId, TermNode, Value};
use axeyum_solver::{ProofOutcome, SolverConfig, UnknownReason, prove, prove_unsat_to_lean_module};

use crate::ast::{ContractProgram, Program, Ty};
use crate::lower::{BadState, LowerError, lower_contract_program, lower_program};

/// A concrete value of one verified-function input, decoded from a bug witness.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Witness {
    /// An integer input: `value` is the unsigned bit-pattern at `width` bits;
    /// `signed` says whether to read it as `iN` (two's complement) when printing
    /// / reproducing.
    Int {
        /// The variable name.
        name: String,
        /// Width in bits.
        width: u32,
        /// Whether the source type was signed (`iN`).
        signed: bool,
        /// The value as an unsigned bit-pattern (masked to `width`).
        bits: u128,
    },
    /// A boolean input.
    Bool {
        /// The variable name.
        name: String,
        /// The value.
        value: bool,
    },
    /// A fixed-length array input.
    Array {
        /// The variable name.
        name: String,
        /// Element width in bits (0 for a bool element list — `bools` then set).
        width: u32,
        /// Whether elements are signed integers.
        signed: bool,
        /// Element bit-patterns (for integer arrays).
        ints: Vec<u128>,
    },
}

impl Witness {
    /// Renders the signed/unsigned decimal value of an integer witness as a
    /// string (for diagnostics and generated-test literals).
    #[must_use]
    pub fn render_int(width: u32, signed: bool, bits: u128) -> String {
        if signed {
            signed_value(width, bits).to_string()
        } else {
            bits.to_string()
        }
    }
}

/// Reinterprets an unsigned `width`-bit pattern as a two's-complement signed
/// value. Every width in `1..=128` is exact, including `i128::MIN`.
#[must_use]
pub fn signed_value(width: u32, bits: u128) -> i128 {
    if width == 0 || width > 128 {
        // Invalid source widths are rejected before replay. Keep this helper
        // total for direct callers without inventing a signed interpretation.
        return i128::try_from(bits & (i128::MAX as u128)).unwrap_or(0);
    }
    let mask = if width == 128 {
        u128::MAX
    } else {
        (1_u128 << width) - 1
    };
    let shift = 128 - width;
    // Move the source sign bit into bit 127, reinterpret the complete bit
    // pattern, then arithmetic-shift it back. This avoids trying to represent
    // positive 2^127 at width 127 and handles width 128 with `shift == 0`.
    ((bits & mask) << shift).cast_signed() >> shift
}

/// The verdict of [`verify_program`].
#[derive(Debug, Clone)]
pub enum Verdict {
    /// No panic-class bad state is reachable within the unwind bound. Carries
    /// whether an independently re-checked certificate was produced, and — the
    /// headline moat number — a self-contained Lean 4 module that re-proves the
    /// refutation (`None` when the safety proof's fragment is outside the Lean
    /// reconstructor, never a false promise).
    Verified {
        /// `true` iff the safety proof's certificate re-verified.
        certified: bool,
        /// A Lean 4 module re-proving the bounded-safety refutation, when the
        /// fragment is Lean-reconstructable; `None` otherwise. Present iff the
        /// result is *Lean-certified* (the moat metric `cert_coverage` counts).
        lean_module: Option<String>,
    },
    /// A concrete input reaching a bug: the witness plus the offending class.
    Counterexample {
        /// The bug class label (e.g. `"add overflow"`).
        class: String,
        /// The concrete inputs (in declaration order).
        inputs: Vec<Witness>,
    },
    /// The check did not conclude within budget, or the body left the supported
    /// fragment. Never a wrong verdict.
    Unknown {
        /// A human-readable reason.
        reason: String,
    },
}

/// Lowers and decides a [`Program`].
///
/// # Errors
///
/// Returns a [`axeyum_solver::SolverError`] only if the underlying engine raises a hard error
/// (a failed self-check is a soundness alarm); ordinary lowering or
/// undecidability is reported as a [`Verdict::Unknown`], not an error.
pub fn verify_program(
    program: &Program,
    config: &SolverConfig,
) -> Result<Verdict, axeyum_solver::SolverError> {
    let mut arena = TermArena::new();
    let lowered = match lower_program(&mut arena, program) {
        Ok(l) => l,
        Err(e) => {
            return Ok(Verdict::Unknown {
                reason: lower_unknown_reason(&e),
            });
        }
    };

    if lowered.bad_states.is_empty() {
        // No panic class anywhere in the body: trivially verified (vacuously, no
        // certificate to re-check, no proof to reconstruct).
        return Ok(Verdict::Verified {
            certified: false,
            lean_module: None,
        });
    }

    // Per bad state, also keep its label so a witness can name the class. We pose
    // the disjunction once for the verdict, then (on sat) re-pose each disjunct to
    // attribute the class.
    let mut disjuncts: Vec<axeyum_ir::TermId> = Vec::with_capacity(lowered.bad_states.len());
    for bs in &lowered.bad_states {
        disjuncts.push(bs.term);
    }
    let any_bad = or_all(&mut arena, &disjuncts)?;
    let goal = arena.not(any_bad)?; // safety goal: no bad state reachable

    match prove(&mut arena, &[], goal, config)? {
        ProofOutcome::Proved(report) => {
            // `prove` re-checks the certificate before returning `Proved` (its
            // contract: "untrusted search, trusted small checking"), so a
            // `Proved` here is an independently re-verified safety proof. We then
            // re-run the check ourselves against `[any_bad]` (the refuted query)
            // as an extra, in-crate confirmation.
            let certified = report.evidence.check(&arena, &[any_bad]).unwrap_or(false);
            // Best-effort Lean module over the refuted query (`any_bad` must be
            // unsat for safety). Mirror the property SDK: flatten top-level
            // conjuncts / strip `¬¬` so the QF_BV reconstructor sees the shape it
            // keys off; `None` for fragments it does not cover — never a false
            // promise (U1/U4 cap how broad this is).
            let lean_module = if certified {
                let flat = flatten_conjuncts(&arena, &[any_bad]);
                prove_unsat_to_lean_module(&mut arena, &flat)
                    .ok()
                    .map(|(_, module)| module)
            } else {
                None
            };
            Ok(Verdict::Verified {
                certified,
                lean_module,
            })
        }
        ProofOutcome::Disproved(model) => {
            let class = attribute_class(&lowered.bad_states, &model, &arena);
            let inputs = lift_inputs(&lowered, &model);
            Ok(Verdict::Counterexample { class, inputs })
        }
        ProofOutcome::Unknown(reason) => Ok(Verdict::Unknown {
            reason: format!("{reason:?}"),
        }),
    }
}

/// Lowers and decides one source-level scalar contract.
///
/// Panic bad states are guarded by the precondition. The postcondition is
/// checked only on normal return, and its counterexample class remains distinct
/// so macro-generated replay can validate a returned value instead of expecting
/// a panic.
///
/// # Errors
///
/// Returns a solver error only for a hard engine failure. Lowering failures,
/// unsatisfiable preconditions, and undecided checks are [`Verdict::Unknown`].
pub fn verify_contract_program(
    contract: &ContractProgram,
    config: &SolverConfig,
) -> Result<Verdict, axeyum_solver::SolverError> {
    let mut arena = TermArena::new();
    let mut lowered = match lower_contract_program(&mut arena, contract) {
        Ok(lowered) => lowered,
        Err(error) => {
            return Ok(Verdict::Unknown {
                reason: lower_unknown_reason(&error),
            });
        }
    };
    let not_requires = arena.not(lowered.requires)?;
    match prove(&mut arena, &[], not_requires, config)? {
        ProofOutcome::Proved(_) => {
            return Ok(Verdict::Unknown {
                reason: "invalid contract: precondition is unsatisfiable".into(),
            });
        }
        ProofOutcome::Unknown(reason) => {
            return Ok(Verdict::Unknown {
                reason: format!("contract precondition satisfiability undecided: {reason:?}"),
            });
        }
        ProofOutcome::Disproved(_) => {}
    }

    let raw_panic = or_all(
        &mut arena,
        &lowered
            .program
            .bad_states
            .iter()
            .map(|bad| bad.term)
            .collect::<Vec<_>>(),
    )?;
    if !lowered.postcondition_bad_states.is_empty() {
        let normal = arena.not(raw_panic)?;
        let admitted_normal = arena.and(lowered.requires, normal)?;
        let mut postcondition_panic_terms = Vec::new();
        for bad in &lowered.postcondition_bad_states {
            postcondition_panic_terms.push(arena.and(admitted_normal, bad.term)?);
        }
        let any_postcondition_panic = or_all(&mut arena, &postcondition_panic_terms)?;
        let postcondition_total = arena.not(any_postcondition_panic)?;
        match prove(&mut arena, &[], postcondition_total, config)? {
            ProofOutcome::Proved(_) => {}
            ProofOutcome::Disproved(_) => {
                return Ok(Verdict::Unknown {
                    reason:
                        "invalid contract: postcondition may panic on an admitted normal return"
                            .into(),
                });
            }
            ProofOutcome::Unknown(reason) => {
                return Ok(Verdict::Unknown {
                    reason: format!("contract postcondition totality undecided: {reason:?}"),
                });
            }
        }
    }
    for bad in &mut lowered.program.bad_states {
        bad.term = arena.and(lowered.requires, bad.term)?;
    }
    let normal = arena.not(raw_panic)?;
    let post_failed = arena.not(lowered.ensures)?;
    let reached_normal = arena.and(lowered.requires, normal)?;
    let post_failed = arena.and(reached_normal, post_failed)?;
    lowered.program.bad_states.push(BadState {
        label: "postcondition violated".into(),
        term: post_failed,
    });
    let bad_terms = lowered
        .program
        .bad_states
        .iter()
        .map(|bad| bad.term)
        .collect::<Vec<_>>();
    let any_bad = or_all(&mut arena, &bad_terms)?;
    let goal = arena.not(any_bad)?;
    match prove(&mut arena, &[], goal, config)? {
        ProofOutcome::Proved(report) => {
            let certified = report.evidence.check(&arena, &[any_bad]).unwrap_or(false);
            let lean_module = if certified {
                let flat = flatten_conjuncts(&arena, &[any_bad]);
                prove_unsat_to_lean_module(&mut arena, &flat)
                    .ok()
                    .map(|(_, module)| module)
            } else {
                None
            };
            Ok(Verdict::Verified {
                certified,
                lean_module,
            })
        }
        ProofOutcome::Disproved(model) => Ok(Verdict::Counterexample {
            class: attribute_class(&lowered.program.bad_states, &model, &arena),
            inputs: lift_inputs(&lowered.program, &model),
        }),
        ProofOutcome::Unknown(reason) => Ok(Verdict::Unknown {
            reason: format!("{reason:?}"),
        }),
    }
}

/// Splits each assertion into its top-level conjuncts, stripping double
/// negations (`¬¬x → x`), so the result is a flat list whose conjunction is
/// logically equivalent to `assertions`. The `QF_BV` Lean reconstructor keys off
/// separate top-level conjuncts, so this widens the fragment for which a Lean
/// module is emitted without changing the query's meaning. (Same shaping the
/// `axeyum-property` SDK applies as the U1 client-side workaround.)
fn flatten_conjuncts(arena: &TermArena, assertions: &[TermId]) -> Vec<TermId> {
    let mut out = Vec::with_capacity(assertions.len());
    let mut stack: Vec<TermId> = assertions.iter().rev().copied().collect();
    while let Some(t) = stack.pop() {
        match arena.node(t) {
            TermNode::App {
                op: Op::BoolAnd,
                args,
            } => {
                for &arg in args.iter().rev() {
                    stack.push(arg);
                }
            }
            TermNode::App {
                op: Op::BoolNot,
                args,
            } if args.len() == 1 => {
                if let TermNode::App {
                    op: Op::BoolNot,
                    args: inner,
                } = arena.node(args[0])
                    && inner.len() == 1
                {
                    stack.push(inner[0]);
                    continue;
                }
                out.push(t);
            }
            // Drop a literal `true` conjunct (`path ∧ pred` carries a leading
            // `true` from the empty path condition); it is a no-op in the
            // conjunction and the QF_BV reconstructor declines lists with it.
            TermNode::BoolConst(true) => {}
            _ => out.push(t),
        }
    }
    out
}

/// Disjunction of `terms` (`false` if empty; the single term if one).
fn or_all(
    arena: &mut TermArena,
    terms: &[axeyum_ir::TermId],
) -> Result<axeyum_ir::TermId, axeyum_solver::SolverError> {
    let mut iter = terms.iter().copied();
    let Some(first) = iter.next() else {
        return Ok(arena.bool_const(false));
    };
    let mut acc = first;
    for t in iter {
        acc = arena.or(acc, t)?;
    }
    Ok(acc)
}

/// Finds which bad state the witness satisfies (for the class label). Evaluates
/// each bad-state term under the model; the first that holds names the class.
fn attribute_class(
    bad_states: &[crate::lower::BadState],
    model: &axeyum_solver::Model,
    arena: &TermArena,
) -> String {
    let assignment = model.to_assignment();
    for bs in bad_states {
        if let Ok(Value::Bool(true)) = axeyum_ir::eval(arena, bs.term, &assignment) {
            return bs.label.clone();
        }
    }
    bad_states
        .first()
        .map_or_else(|| "unknown bug class".to_string(), |b| b.label.clone())
}

/// Lifts the model into concrete typed witnesses, in declaration order.
fn lift_inputs(lowered: &crate::lower::Lowered, model: &axeyum_solver::Model) -> Vec<Witness> {
    let mut out = Vec::new();
    for (name, sym, ty) in &lowered.param_syms {
        out.push(lift_scalar(name, *sym, *ty, model));
    }
    for (name, syms, ty) in &lowered.array_syms {
        let Ty::Int { width, signed } = *ty else {
            // Phase 1 array elements are integers; a bool array is unsupported and
            // would have been rejected at lowering.
            continue;
        };
        let ints = syms
            .iter()
            .map(|s| match model.get(*s) {
                Some(Value::Bv { value, .. }) => value,
                _ => 0,
            })
            .collect();
        out.push(Witness::Array {
            name: name.clone(),
            width,
            signed,
            ints,
        });
    }
    out
}

fn lift_scalar(
    name: &str,
    sym: axeyum_ir::SymbolId,
    ty: Ty,
    model: &axeyum_solver::Model,
) -> Witness {
    match ty {
        Ty::Int { width, signed } => {
            let bits = match model.get(sym) {
                Some(Value::Bv { value, .. }) => value,
                _ => 0, // don't-care: any value witnesses the bug
            };
            Witness::Int {
                name: name.to_string(),
                width,
                signed,
                bits,
            }
        }
        Ty::Bool => {
            let value = matches!(model.get(sym), Some(Value::Bool(true)));
            Witness::Bool {
                name: name.to_string(),
                value,
            }
        }
    }
}

fn lower_unknown_reason(e: &LowerError) -> String {
    match e {
        LowerError::Unsupported(m) => format!("out of supported fragment: {m}"),
        other => format!("lowering could not model the body: {other}"),
    }
}

/// The Lean-certificate coverage of a set of verdicts: the headline moat metric
/// (the artifact Kani/CBMC cannot produce). Counts, over the **`Verified`**
/// verdicts only, the fraction whose safety proof carried a Lean 4 module.
///
/// `Counterexample`/`Unknown` verdicts are excluded from the denominator (there
/// is no safety proof to certify); a vacuously-verified function — one with no
/// reachable panic class, hence no certificate — counts as verified-but-uncertified.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CertCoverage {
    /// Number of `Verified` verdicts.
    pub verified: usize,
    /// Of those, how many re-checked their certificate (`certified == true`).
    pub certified: usize,
    /// Of those, how many additionally carried a Lean 4 module.
    pub lean_certified: usize,
}

impl CertCoverage {
    /// Fraction of `Verified` results carrying a Lean module (`0.0` if none
    /// verified). The headline moat number.
    #[must_use]
    pub fn lean_fraction(self) -> f64 {
        if self.verified == 0 {
            0.0
        } else {
            f64::from(u32::try_from(self.lean_certified).unwrap_or(u32::MAX))
                / f64::from(u32::try_from(self.verified).unwrap_or(u32::MAX))
        }
    }
}

/// Tallies the [`CertCoverage`] over a set of verdicts.
#[must_use]
pub fn cert_coverage<'a>(verdicts: impl IntoIterator<Item = &'a Verdict>) -> CertCoverage {
    let mut cov = CertCoverage {
        verified: 0,
        certified: 0,
        lean_certified: 0,
    };
    for v in verdicts {
        if let Verdict::Verified {
            certified,
            lean_module,
        } = v
        {
            cov.verified += 1;
            if *certified {
                cov.certified += 1;
            }
            if lean_module.is_some() {
                cov.lean_certified += 1;
            }
        }
    }
    cov
}

/// A default config for `#[verify]`: a deterministic resource budget so the
/// check terminates and is reproducible across machines.
#[must_use]
pub fn default_config() -> SolverConfig {
    SolverConfig {
        resource_limit: Some(50_000_000),
        ..SolverConfig::default()
    }
}

/// Classifies a verdict's `Unknown` reason from a raw [`UnknownReason`] for
/// reporting (kept for the macro's diagnostics).
#[must_use]
pub fn describe_unknown(reason: &UnknownReason) -> String {
    format!("{reason:?}")
}
