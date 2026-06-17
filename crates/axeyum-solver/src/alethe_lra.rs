//! Arithmetic (`la_generic`) Alethe proof checking by direct LRA validity.
//!
//! An Alethe `la_generic` step `(step t (cl l1 … ln) :rule la_generic :args (…))`
//! asserts that the clause `l1 ∨ … ∨ ln` of linear-arithmetic literals is **valid**
//! (a tautology), witnessed by Farkas coefficients in `:args`. Rather than checking
//! the supplied coefficients (subtle), this checker verifies the conclusion
//! **directly**: the clause is valid iff `¬l1 ∧ … ∧ ¬ln` is UNSAT. That conjunction
//! is decided by [`crate::check_with_lra`] (exact-rational simplex with self-checked
//! Farkas certificates), so the step is accepted only when the clause genuinely
//! follows. The `:args` coefficients are an ignored hint we re-derive.
//!
//! This is a SOUNDNESS-CRITICAL proof checker. A literal that does not parse as
//! linear real arithmetic — or a query the LRA engine reports `Unknown` for —
//! cannot be validated, so the step is **rejected** (reported `Some(false)`), never
//! blessed. [`check_alethe_lra`] plugs this into [`axeyum_cnf::check_alethe_with`]
//! as the `extra` callback, keeping `axeyum-cnf` free of any arithmetic dependency.

use std::collections::BTreeMap;

use axeyum_cnf::{AletheCommand, AletheError, AletheLit, AletheTerm};
use axeyum_ir::{Rational, TermArena, TermId};

use crate::backend::CheckResult;
use crate::lra::check_with_lra;

/// Checks an Alethe proof, validating `la_generic` linear-arithmetic steps by
/// direct LRA refutation in addition to the rules [`axeyum_cnf::check_alethe`]
/// handles natively.
///
/// Returns `Ok(true)` when a verified step derives the empty clause (UNSAT
/// established), `Ok(false)` when every command checks but the empty clause is
/// never derived, and `Err` otherwise — see [`axeyum_cnf::check_alethe_with`].
///
/// # Errors
///
/// Returns [`AletheError::UnknownPremise`] for a missing premise id,
/// [`AletheError::UnsupportedRule`] for a rule neither the resolution checker nor
/// the `la_generic` callback handles, and [`AletheError::StepNotEntailed`] for a
/// step whose conclusion does not follow (including a `la_generic` clause that is
/// not a linear-arithmetic tautology, or one this checker cannot validate).
pub fn check_alethe_lra(commands: &[AletheCommand]) -> Result<bool, AletheError> {
    axeyum_cnf::check_alethe_with(commands, &la_generic_check)
}

/// The `extra`-callback for [`axeyum_cnf::check_alethe_with`]: validates the
/// linear-arithmetic rules.
///
/// Returns `None` for any rule other than `la_generic` (so the host reports it as
/// unsupported). For `la_generic`, builds `¬l1 ∧ … ∧ ¬ln` over a fresh
/// [`TermArena`] and decides it with [`check_with_lra`]: `Some(true)` when `Unsat`
/// (the clause is a tautology), `Some(false)` when `Sat` (not a tautology). Any
/// `Unknown`, unsupported-fragment, or unparseable literal yields `Some(false)` —
/// an unvalidatable step is rejected, never accepted (the sound default).
fn la_generic_check(rule: &str, clause: &[AletheLit]) -> Option<bool> {
    if rule != "la_generic" {
        return None;
    }
    Some(la_generic_is_valid(clause))
}

/// Returns `true` iff the linear-arithmetic clause `l1 ∨ … ∨ ln` is valid, decided
/// as `¬l1 ∧ … ∧ ¬ln` being UNSAT. Returns `false` on satisfiable, unknown, or any
/// parse/fragment failure (the sound default for a proof checker).
fn la_generic_is_valid(clause: &[AletheLit]) -> bool {
    let mut arena = TermArena::new();
    let mut vars: BTreeMap<String, TermId> = BTreeMap::new();
    let mut assertions = Vec::with_capacity(clause.len());
    for lit in clause {
        match negated_literal_term(&mut arena, &mut vars, lit) {
            Some(term) => assertions.push(term),
            // A literal outside linear real arithmetic ⇒ we cannot validate ⇒ reject.
            None => return false,
        }
    }
    // An empty clause is `false`; its negation is the empty conjunction `true`,
    // which is trivially satisfiable, so the clause is not valid. The LRA engine
    // would report `sat` on no assertions, but short-circuit for clarity.
    if assertions.is_empty() {
        return false;
    }
    matches!(check_with_lra(&arena, &assertions), Ok(CheckResult::Unsat))
}

/// Builds the IR Boolean term for `¬lit`. The clause literal `lit` is `{atom,
/// negated}`; `¬lit` is the comparison `atom` as-is when `lit.negated`, else the
/// IR negation of that comparison. Returns `None` if the atom is not a supported
/// linear-arithmetic comparison.
fn negated_literal_term(
    arena: &mut TermArena,
    vars: &mut BTreeMap<String, TermId>,
    lit: &AletheLit,
) -> Option<TermId> {
    let comparison = comparison_term(arena, vars, &lit.atom)?;
    if lit.negated {
        Some(comparison)
    } else {
        arena.not(comparison).ok()
    }
}

/// Builds the IR Boolean comparison for an atom `App(head, [a, b])` with `head ∈
/// {<=, <, >=, >, =}` over linear real operands. Returns `None` otherwise.
fn comparison_term(
    arena: &mut TermArena,
    vars: &mut BTreeMap<String, TermId>,
    atom: &AletheTerm,
) -> Option<TermId> {
    let AletheTerm::App(head, args) = atom else {
        return None;
    };
    if args.len() != 2 {
        return None;
    }
    let left = real_term(arena, vars, &args[0])?;
    let right = real_term(arena, vars, &args[1])?;
    match head.as_str() {
        "<=" => arena.real_le(left, right).ok(),
        "<" => arena.real_lt(left, right).ok(),
        ">=" => arena.real_ge(left, right).ok(),
        ">" => arena.real_gt(left, right).ok(),
        "=" => arena.eq(left, right).ok(),
        _ => None,
    }
}

/// Lowers an [`AletheTerm`] to an IR real-sorted term. A `Const` is a numeral (if
/// it parses) or a fresh real variable (memoized by name). An `App` over `{+, -,
/// *}` builds the corresponding linear arithmetic; `*` requires at least one
/// constant factor (nonlinear ⇒ `None`). Anything else ⇒ `None`.
fn real_term(
    arena: &mut TermArena,
    vars: &mut BTreeMap<String, TermId>,
    term: &AletheTerm,
) -> Option<TermId> {
    match term {
        AletheTerm::Const(symbol) => {
            if let Some(rational) = parse_rational(symbol) {
                Some(arena.real_const(rational))
            } else {
                Some(real_var(arena, vars, symbol))
            }
        }
        AletheTerm::App(head, args) => match head.as_str() {
            "+" => fold_real(arena, vars, args, TermArena::real_add),
            "*" => fold_real_mul(arena, vars, args),
            "-" => match args.len() {
                1 => {
                    let a = real_term(arena, vars, &args[0])?;
                    arena.real_neg(a).ok()
                }
                n if n >= 2 => fold_real(arena, vars, args, TermArena::real_sub),
                _ => None,
            },
            _ => None,
        },
    }
}

/// A fresh real variable for `name`, memoized so repeated names share one symbol.
fn real_var(arena: &mut TermArena, vars: &mut BTreeMap<String, TermId>, name: &str) -> TermId {
    if let Some(&existing) = vars.get(name) {
        return existing;
    }
    // `real_var` declares the symbol (idempotent for a given name+sort) and returns
    // its variable term; declaring `Sort::Real` cannot conflict here because every
    // name in this map is only ever declared real.
    let term = arena
        .real_var(name)
        .expect("fresh real variable declaration");
    vars.insert(name.to_owned(), term);
    term
}

/// Left-folds an n-ary `+`/`-` over real operands with the given binary builder
/// (requires at least one operand). Returns `None` if any operand fails to parse or
/// the builder errors.
fn fold_real(
    arena: &mut TermArena,
    vars: &mut BTreeMap<String, TermId>,
    args: &[AletheTerm],
    build: fn(&mut TermArena, TermId, TermId) -> Result<TermId, axeyum_ir::IrError>,
) -> Option<TermId> {
    let (first, rest) = args.split_first()?;
    let mut acc = real_term(arena, vars, first)?;
    for arg in rest {
        let next = real_term(arena, vars, arg)?;
        acc = build(arena, acc, next).ok()?;
    }
    Some(acc)
}

/// Left-folds an n-ary `*` over real operands, requiring the result to stay linear:
/// at most one folded sub-product may be non-constant. We enforce this by requiring
/// every multiplication to have at least one constant factor at fold time, which —
/// since constants fold to constants — keeps the whole product linear. Returns
/// `None` on a nonlinear product or any parse failure.
fn fold_real_mul(
    arena: &mut TermArena,
    vars: &mut BTreeMap<String, TermId>,
    args: &[AletheTerm],
) -> Option<TermId> {
    let (first, rest) = args.split_first()?;
    let mut acc = real_term(arena, vars, first)?;
    let mut acc_is_const = is_constant_term(arena, acc);
    for arg in rest {
        let next = real_term(arena, vars, arg)?;
        let next_is_const = is_constant_term(arena, next);
        // Linear product: at least one of the two factors must be a constant.
        if !acc_is_const && !next_is_const {
            return None;
        }
        acc = arena.real_mul(acc, next).ok()?;
        // The product is constant only when both factors were constant.
        acc_is_const = acc_is_const && next_is_const;
    }
    Some(acc)
}

/// Whether `term` is a real constant.
fn is_constant_term(arena: &TermArena, term: TermId) -> bool {
    matches!(arena.node(term), axeyum_ir::TermNode::RealConst(_))
}

/// Parses an SMT-LIB numeral into an exact [`Rational`]: a decimal integer
/// (`"3"`, `"-2"`) or a fixed-point decimal (`"1.5"`, `"-0.25"`). Returns `None`
/// for anything else (so such a `Const` is treated as a variable, or — inside a
/// `*` linearity check — keeps the product nonlinear).
fn parse_rational(text: &str) -> Option<Rational> {
    if text.is_empty() {
        return None;
    }
    let (negative, body) = match text.strip_prefix('-') {
        Some(rest) => (true, rest),
        None => (false, text),
    };
    if body.is_empty() {
        return None;
    }
    let rational = match body.split_once('.') {
        None => Rational::integer(body.parse::<i128>().ok()?),
        Some((int_part, frac_part)) => {
            // Both sides must be ASCII digits (possibly empty, e.g. "1." or ".5").
            if int_part.is_empty() && frac_part.is_empty() {
                return None;
            }
            if !int_part
                .bytes()
                .chain(frac_part.bytes())
                .all(|b| b.is_ascii_digit())
            {
                return None;
            }
            let int_value: i128 = if int_part.is_empty() {
                0
            } else {
                int_part.parse().ok()?
            };
            let frac_digits = frac_part.len();
            let denominator = 10i128.checked_pow(u32::try_from(frac_digits).ok()?)?;
            let frac_value: i128 = if frac_part.is_empty() {
                0
            } else {
                frac_part.parse().ok()?
            };
            let scaled = int_value
                .checked_mul(denominator)?
                .checked_add(frac_value)?;
            Rational::new(scaled, denominator)
        }
    };
    Some(if negative {
        Rational::zero() - rational
    } else {
        rational
    })
}

#[cfg(test)]
mod tests {
    use super::check_alethe_lra;
    use axeyum_cnf::{AletheCommand, AletheError, AletheLit, AletheTerm};

    fn num(value: &str) -> AletheTerm {
        AletheTerm::Const(value.to_owned())
    }

    fn var(name: &str) -> AletheTerm {
        AletheTerm::Const(name.to_owned())
    }

    fn cmp(head: &str, a: AletheTerm, b: AletheTerm) -> AletheLit {
        AletheLit {
            atom: AletheTerm::App(head.to_owned(), vec![a, b]),
            negated: false,
        }
    }

    /// The negated-polarity comparison over the same atom (for resolution, which
    /// cancels a positive and negative literal over a *structurally identical*
    /// atom — it has no theory knowledge of comparison semantics).
    fn ncmp(head: &str, a: AletheTerm, b: AletheTerm) -> AletheLit {
        AletheLit {
            negated: true,
            ..cmp(head, a, b)
        }
    }

    fn step(id: &str, clause: Vec<AletheLit>, rule: &str, premises: &[&str]) -> AletheCommand {
        AletheCommand::Step {
            id: id.to_owned(),
            clause,
            rule: rule.to_owned(),
            premises: premises.iter().map(|p| (*p).to_owned()).collect(),
        }
    }

    fn assume(id: &str, clause: Vec<AletheLit>) -> AletheCommand {
        AletheCommand::Assume {
            id: id.to_owned(),
            clause,
        }
    }

    #[test]
    fn la_generic_accepts_a_valid_arithmetic_tautology() {
        // (cl (< x 1) (> x 0)) is valid: its negation x>=1 ∧ x<=0 is UNSAT.
        // The lone la_generic step verifies (no empty clause) ⇒ Ok(false), i.e.
        // checked, not refuted. The point is it does NOT error.
        let clause = vec![cmp("<", var("x"), num("1")), cmp(">", var("x"), num("0"))];
        let proof = vec![step("t1", clause, "la_generic", &[])];
        assert_eq!(
            check_alethe_lra(&proof),
            Ok(false),
            "a valid LA tautology must be accepted (verified, not refuted)"
        );
    }

    #[test]
    fn la_generic_rejects_a_non_tautology() {
        // (cl (< x 1) (> x 2)) is NOT valid: its negation x>=1 ∧ x<=2 is SAT
        // (e.g. x = 1.5). The step must be rejected as not entailed.
        let clause = vec![cmp("<", var("x"), num("1")), cmp(">", var("x"), num("2"))];
        let proof = vec![step("t1", clause, "la_generic", &[])];
        assert_eq!(
            check_alethe_lra(&proof),
            Err(AletheError::StepNotEntailed {
                id: "t1".to_owned()
            }),
            "a non-tautology must be REJECTED (the soundness property)"
        );
    }

    #[test]
    fn la_generic_end_to_end_refutation() {
        // Assume x <= 0 and 1 <= x (contradictory). A la_generic step derives the
        // clause (cl (not (<= x 0)) (not (<= 1 x))) — valid because its negation
        // (<= x 0) ∧ (<= 1 x) is UNSAT. The la_generic clause uses the *same atoms*
        // with flipped polarity, so propositional resolution against the two
        // assumes cancels both literals to the empty clause (resolution has no
        // theory knowledge; it matches atoms structurally).
        let a1 = cmp("<=", var("x"), num("0")); // x <= 0
        let a2 = cmp("<=", num("1"), var("x")); // 1 <= x
        // The la_generic clause: negated-polarity over those very atoms.
        let n1 = ncmp("<=", var("x"), num("0")); // (not (<= x 0))
        let n2 = ncmp("<=", num("1"), var("x")); // (not (<= 1 x))
        let proof = vec![
            assume("h1", vec![a1]),
            assume("h2", vec![a2]),
            // The LA tautology clause (the negations of the assumed literals).
            step("la", vec![n1, n2], "la_generic", &[]),
            // Resolve: {(¬(<=x 0) ∨ ¬(<=1 x)), (<=x 0), (<=1 x)} ⊨ () — empty clause.
            step("done", vec![], "resolution", &["la", "h1", "h2"]),
        ];
        assert_eq!(
            check_alethe_lra(&proof),
            Ok(true),
            "the la_generic clause plus its premises must refute to the empty clause"
        );
    }

    #[test]
    fn unknown_rule_still_unsupported() {
        // A rule the la_generic callback does not know (returns None) stays
        // unsupported.
        let proof = vec![step(
            "s1",
            vec![cmp("<", var("x"), num("1"))],
            "made_up",
            &[],
        )];
        assert_eq!(
            check_alethe_lra(&proof),
            Err(AletheError::UnsupportedRule {
                rule: "made_up".to_owned()
            })
        );
    }

    #[test]
    fn la_generic_rejects_nonlinear_literal() {
        // (cl (< (* x x) 1)) — nonlinear, cannot be lowered ⇒ rejected (sound).
        let nonlinear = AletheLit {
            atom: AletheTerm::App(
                "<".to_owned(),
                vec![
                    AletheTerm::App("*".to_owned(), vec![var("x"), var("x")]),
                    num("1"),
                ],
            ),
            negated: false,
        };
        let proof = vec![step("t1", vec![nonlinear], "la_generic", &[])];
        assert_eq!(
            check_alethe_lra(&proof),
            Err(AletheError::StepNotEntailed {
                id: "t1".to_owned()
            }),
            "an unparseable (nonlinear) literal must be rejected, never blessed"
        );
    }
}
