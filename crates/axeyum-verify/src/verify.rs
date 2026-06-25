//! The verifier: lower a [`Program`], ask the solver whether any panic-class
//! bad state is reachable, and report a verdict.
//!
//! A bug is reachable iff `OR(bad_states)` is satisfiable. We pose this to
//! [`axeyum_solver::prove`] as: prove the goal `¬OR(bad_states)`. An `unsat`
//! refutation of `OR(bad_states)` is a **bounded-safety proof** carrying a
//! re-checked certificate; a `sat` model is a concrete **bug witness**, lifted
//! into typed inputs; `unknown` is surfaced honestly.

use axeyum_ir::{TermArena, Value};
use axeyum_solver::{ProofOutcome, SolverConfig, UnknownReason, prove};

use crate::ast::{Program, Ty};
use crate::lower::{LowerError, lower_program};

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
/// value (as an `i128`, which holds any width ≤ 127 exactly).
#[must_use]
pub fn signed_value(width: u32, bits: u128) -> i128 {
    if width == 0 || width > 127 {
        // No room to interpret the sign in i128; return the low bits verbatim.
        return i128::try_from(bits & (i128::MAX as u128)).unwrap_or(0);
    }
    let sign_bit = 1u128 << (width - 1);
    let masked = bits & ((1u128 << width) - 1);
    // `masked < 2^width ≤ 2^127`, so it always fits in i128; the `unwrap_or` is
    // unreachable defensive code (keeps the helper panic-free).
    let magnitude = i128::try_from(masked).unwrap_or(0);
    if masked & sign_bit != 0 {
        // Negative: subtract 2^width.
        magnitude - (1i128 << width)
    } else {
        magnitude
    }
}

/// The verdict of [`verify_program`].
#[derive(Debug, Clone)]
pub enum Verdict {
    /// No panic-class bad state is reachable within the unwind bound. Carries
    /// whether an independently re-checked certificate was produced.
    Verified {
        /// `true` iff the safety proof's certificate re-verified.
        certified: bool,
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
        // certificate to re-check).
        return Ok(Verdict::Verified { certified: false });
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
            Ok(Verdict::Verified { certified })
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
