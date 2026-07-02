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
use axeyum_ir::{Op, Rational, TermArena, TermId, TermNode};

use crate::backend::CheckResult;
use crate::lra::{check_with_lia_simplex, check_with_lra};

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
/// Returns `None` for any rule other than `la_generic`/`lia_generic` (so the host
/// reports it as unsupported). For `la_generic`, builds `¬l1 ∧ … ∧ ¬ln` over a
/// fresh [`TermArena`] and decides it with [`check_with_lra`] (linear **real**
/// arithmetic); for `lia_generic`, builds the **integer** negation and decides it
/// with [`check_with_lia_simplex`] (integer-complete, so it accepts clauses valid
/// only over the integers, e.g. `(cl (<= x 0) (>= x 1))`). Each returns `Some(true)`
/// when the negation is `Unsat` (the clause is a tautology), `Some(false)` when it
/// is `Sat` (not a tautology). Any `Unknown`, unsupported-fragment, or unparseable
/// literal yields `Some(false)` — an unvalidatable step is rejected, never accepted
/// (the sound default).
fn la_generic_check(rule: &str, clause: &[AletheLit]) -> Option<bool> {
    match rule {
        "la_generic" => Some(la_generic_is_valid(clause)),
        "lia_generic" => Some(lia_generic_is_valid(clause)),
        _ => None,
    }
}

/// Crate-internal accessor for [`la_generic_check`]: lets the finite-quantifier
/// certificate checker ([`crate::quant_finite_cert`]) chain the arithmetic rule
/// validation behind its own `forall_inst_guarded` hook, so one checker validates
/// both the instantiation lemma and the `lia_generic` ground refutation.
pub(crate) fn la_generic_check_pub(rule: &str, clause: &[AletheLit]) -> Option<bool> {
    la_generic_check(rule, clause)
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

/// Returns `true` iff the linear-**integer**-arithmetic clause `l1 ∨ … ∨ ln` is
/// valid over the integers, decided as `¬l1 ∧ … ∧ ¬ln` being integer-UNSAT by
/// [`check_with_lia_simplex`]. Unlike [`la_generic_is_valid`], this accounts for
/// integrality, so it accepts clauses valid only over `Int` (e.g.
/// `(cl (<= x 0) (>= x 1))`, whose negation `x > 0 ∧ x < 1` has no integer
/// solution). Returns `false` on satisfiable, unknown, or any parse/fragment
/// failure (the sound default for a proof checker).
fn lia_generic_is_valid(clause: &[AletheLit]) -> bool {
    let mut arena = TermArena::new();
    let mut vars: BTreeMap<String, TermId> = BTreeMap::new();
    let mut assertions = Vec::with_capacity(clause.len());
    for lit in clause {
        match int_negated_literal_term(&mut arena, &mut vars, lit) {
            Some(term) => assertions.push(term),
            // A literal outside linear integer arithmetic ⇒ cannot validate ⇒ reject.
            None => return false,
        }
    }
    // An empty clause is `false`; its negation is the empty conjunction `true`,
    // trivially satisfiable, so the clause is not valid.
    if assertions.is_empty() {
        return false;
    }
    matches!(
        check_with_lia_simplex(&arena, &assertions),
        Ok(CheckResult::Unsat)
    )
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
            // Any other application head — e.g. an uninterpreted-function
            // application `(f c)` — has no linear-arithmetic structure, so for the
            // purposes of `la_generic` validity it is an OPAQUE atom: a single fresh
            // real variable keyed by the term's canonical s-expression, so the same
            // application is the same variable. Treating a maximal non-arithmetic
            // subterm as a fresh variable is exactly congruence-free `EUF`+`LRA`
            // validity; it can only make the `la_generic` check MORE conservative
            // (it never accepts a clause that is not a tautology under this
            // abstraction), so it is sound. This is what lets the `QF_UFLRA`
            // interpolant's opaque-application refutations re-check here.
            _ => Some(real_var(arena, vars, &term.key())),
        },
        // An indexed-operator application (e.g. a bit-blast `(_ @bit_of i)`) has no
        // LRA real meaning; like an uninterpreted application it is an opaque atom,
        // a fresh real variable keyed by its canonical s-expression.
        AletheTerm::Indexed { .. } => Some(real_var(arena, vars, &term.key())),
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
    // Exact fraction `p/q` (the form the LRA proof emitter produces).
    if let Some((num, den)) = body.split_once('/') {
        let n: i128 = num.parse().ok()?;
        let d: i128 = den.parse().ok()?;
        if d == 0 {
            return None;
        }
        let n = if negative { n.checked_neg()? } else { n };
        return Some(Rational::new(n, d));
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
    if negative {
        // Negating a freshly-parsed numeral can overflow only at `i128::MIN`;
        // a literal we cannot represent exactly ⇒ `None` (treated as a variable
        // or a nonlinear factor by the caller — never a wrong proof).
        rational.checked_neg()
    } else {
        Some(rational)
    }
}

/// Integer counterpart of [`negated_literal_term`]: builds the IR Boolean term for
/// `¬lit` over the linear-**integer** fragment, or `None` if the atom is not a
/// supported linear-integer comparison.
fn int_negated_literal_term(
    arena: &mut TermArena,
    vars: &mut BTreeMap<String, TermId>,
    lit: &AletheLit,
) -> Option<TermId> {
    let comparison = int_comparison_term(arena, vars, &lit.atom)?;
    if lit.negated {
        Some(comparison)
    } else {
        arena.not(comparison).ok()
    }
}

/// Integer counterpart of [`comparison_term`]: builds the IR Boolean comparison for
/// an atom `App(head, [a, b])` with `head ∈ {<=, <, >=, >, =}` over linear integer
/// operands. Returns `None` otherwise.
fn int_comparison_term(
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
    let left = int_term(arena, vars, &args[0])?;
    let right = int_term(arena, vars, &args[1])?;
    match head.as_str() {
        "<=" => arena.int_le(left, right).ok(),
        "<" => arena.int_lt(left, right).ok(),
        ">=" => arena.int_ge(left, right).ok(),
        ">" => arena.int_gt(left, right).ok(),
        "=" => arena.eq(left, right).ok(),
        _ => None,
    }
}

/// Integer counterpart of [`real_term`]: lowers an [`AletheTerm`] to an IR
/// integer-sorted term. A `Const` is a plain integer numeral (if it parses as
/// `i128`) or a fresh integer variable (memoized by name). An `App` over `{+, -,
/// *}` builds the corresponding linear arithmetic; `*` requires at least one
/// constant factor (nonlinear ⇒ `None`). Any other application head is treated as
/// an opaque integer variable keyed by its canonical term, matching the real
/// `la_generic` checker's congruence-free UF abstraction.
fn int_term(
    arena: &mut TermArena,
    vars: &mut BTreeMap<String, TermId>,
    term: &AletheTerm,
) -> Option<TermId> {
    match term {
        AletheTerm::Const(symbol) => {
            // Integer numerals are plain integers (no fractions/decimals); a `Const`
            // that does not parse as `i128` is a variable.
            if let Ok(value) = symbol.parse::<i128>() {
                Some(arena.int_const(value))
            } else {
                Some(int_var(arena, vars, symbol))
            }
        }
        AletheTerm::App(head, args) => match head.as_str() {
            "+" => fold_int(arena, vars, args, TermArena::int_add),
            "*" => fold_int_mul(arena, vars, args),
            "-" => match args.len() {
                1 => {
                    let a = int_term(arena, vars, &args[0])?;
                    arena.int_neg(a).ok()
                }
                n if n >= 2 => fold_int(arena, vars, args, TermArena::int_sub),
                _ => None,
            },
            _ => Some(int_var(arena, vars, &term.key())),
        },
        // As with ordinary uninterpreted applications, indexed operators are
        // opaque integer terms for `lia_generic` validity.
        AletheTerm::Indexed { .. } => Some(int_var(arena, vars, &term.key())),
    }
}

/// A fresh integer variable for `name`, memoized so repeated names share one symbol.
fn int_var(arena: &mut TermArena, vars: &mut BTreeMap<String, TermId>, name: &str) -> TermId {
    if let Some(&existing) = vars.get(name) {
        return existing;
    }
    // `int_var` declares the symbol (idempotent for a given name+sort) and returns
    // its variable term; declaring `Sort::Int` cannot conflict here because every
    // name in this map is only ever declared integer.
    let term = arena
        .int_var(name)
        .expect("fresh integer variable declaration");
    vars.insert(name.to_owned(), term);
    term
}

/// Integer counterpart of [`fold_real`]: left-folds an n-ary `+`/`-` over integer
/// operands with the given binary builder (requires at least one operand). Returns
/// `None` if any operand fails to parse or the builder errors.
fn fold_int(
    arena: &mut TermArena,
    vars: &mut BTreeMap<String, TermId>,
    args: &[AletheTerm],
    build: fn(&mut TermArena, TermId, TermId) -> Result<TermId, axeyum_ir::IrError>,
) -> Option<TermId> {
    let (first, rest) = args.split_first()?;
    let mut acc = int_term(arena, vars, first)?;
    for arg in rest {
        let next = int_term(arena, vars, arg)?;
        acc = build(arena, acc, next).ok()?;
    }
    Some(acc)
}

/// Integer counterpart of [`fold_real_mul`]: left-folds an n-ary `*` over integer
/// operands, requiring the result to stay linear by demanding at least one constant
/// factor at every multiplication. Returns `None` on a nonlinear product or any
/// parse failure.
fn fold_int_mul(
    arena: &mut TermArena,
    vars: &mut BTreeMap<String, TermId>,
    args: &[AletheTerm],
) -> Option<TermId> {
    let (first, rest) = args.split_first()?;
    let mut acc = int_term(arena, vars, first)?;
    let mut acc_is_const = is_int_constant_term(arena, acc);
    for arg in rest {
        let next = int_term(arena, vars, arg)?;
        let next_is_const = is_int_constant_term(arena, next);
        // Linear product: at least one of the two factors must be a constant.
        if !acc_is_const && !next_is_const {
            return None;
        }
        acc = arena.int_mul(acc, next).ok()?;
        // The product is constant only when both factors were constant.
        acc_is_const = acc_is_const && next_is_const;
    }
    Some(acc)
}

/// Whether `term` is an integer constant.
fn is_int_constant_term(arena: &TermArena, term: TermId) -> bool {
    matches!(arena.node(term), axeyum_ir::TermNode::IntConst(_))
}

/// Emits a checkable Alethe refutation of an `unsat` linear-real-arithmetic
/// conjunction `assertions`, or `None` if they are not `unsat` (by
/// [`check_with_lra`]) or any atom is outside the linear-real fragment the term
/// converter covers.
///
/// The proof assumes each atom `φᵢ`, derives the tautology clause
/// `(cl ¬φ1 … ¬φn)` by **`la_generic`** (valid because `⋀ φᵢ` is `unsat`), and
/// resolves it against the assumes to the empty clause. It is **self-validated**:
/// the assembled proof is run through [`check_alethe_lra`] and returned only if it
/// checks — so a construction bug yields `None`, never a wrong proof. This is the
/// emission counterpart to the `la_generic` checker (the "trusted small checking"
/// identity for linear real arithmetic).
#[must_use]
pub fn prove_lra_unsat_alethe(
    arena: &TermArena,
    assertions: &[TermId],
) -> Option<Vec<AletheCommand>> {
    // Only a genuine LRA refutation has a proof.
    if !matches!(check_with_lra(arena, assertions), Ok(CheckResult::Unsat)) {
        return None;
    }
    // Convert each atom to an Alethe comparison; bail if any is outside the fragment.
    let atoms: Vec<AletheTerm> = assertions
        .iter()
        .map(|&a| real_atom_to_alethe(arena, a))
        .collect::<Option<Vec<_>>>()?;
    if atoms.is_empty() {
        return None;
    }

    let mut commands = Vec::with_capacity(atoms.len() + 2);
    let mut premise_ids: Vec<String> = Vec::with_capacity(atoms.len());
    // Assume each atom `φᵢ` as the unit clause `(cl φᵢ)`.
    for (i, atom) in atoms.iter().enumerate() {
        let id = format!("h{i}");
        commands.push(AletheCommand::Assume {
            id: id.clone(),
            clause: vec![AletheLit {
                atom: atom.clone(),
                negated: false,
            }],
        });
        premise_ids.push(id);
    }
    // `la_generic` derives `(cl ¬φ1 … ¬φn)` — valid since `⋀ φᵢ` is unsat.
    let la_clause: Vec<AletheLit> = atoms
        .iter()
        .map(|atom| AletheLit {
            atom: atom.clone(),
            negated: true,
        })
        .collect();
    // Derive the per-assertion Farkas `:args` from the certificate: one signed
    // coefficient per assertion (inequalities and equalities both covered; see
    // `farkas_args`). Empty only for shapes we cannot reduce to one coefficient —
    // our own checker still accepts the proof, Carcara then reports it `invalid`.
    let args = farkas_args(arena, assertions);
    commands.push(AletheCommand::Step {
        id: "la".to_owned(),
        clause: la_clause,
        rule: "la_generic".to_owned(),
        premises: Vec::new(),
        args,
    });
    // Resolve the la_generic clause against every assume to the empty clause.
    let mut resolution_premises = vec!["la".to_owned()];
    resolution_premises.extend(premise_ids);
    commands.push(AletheCommand::Step {
        id: "empty".to_owned(),
        clause: Vec::new(),
        rule: "resolution".to_owned(),
        premises: resolution_premises,
        args: Vec::new(),
    });

    // Self-validate: return the proof only if it checks (and derives `(cl)`).
    if matches!(check_alethe_lra(&commands), Ok(true)) {
        Some(commands)
    } else {
        None
    }
}

/// Emits a checkable Alethe `la_generic` refutation of an `unsat` **congruence-free**
/// `QF_UFLRA` conjunction — a conjunction of linear-real comparisons whose only
/// uninterpreted-function applications act as **opaque** shared reals (no functional
/// consistency / congruence is needed for the contradiction) — or `None` otherwise.
///
/// Each uninterpreted-function application `f(args)` is treated as an opaque real:
/// the conjunction is abstracted (every distinct application → one fresh real
/// variable, via [`axeyum_rewrite::eliminate_functions`]'s congruence-free
/// abstraction), [`prove_lra_unsat_alethe`] refutes the **pure-`LRA`** abstraction
/// (so the exact-rational `Farkas` decision and `:args` machinery apply unchanged),
/// and each fresh-variable `Const` is then substituted **back** to its original
/// application term in the emitted proof's atoms. The result refutes the *original*
/// conjunction with each application rendered verbatim as `(f args)`.
///
/// The proof is **self-validated** through [`check_alethe_lra`] (whose `la_generic`
/// check now treats a maximal non-arithmetic subterm — including `(f args)` — as an
/// opaque fresh real, congruence-free `EUF`+`LRA` validity) and returned only if it
/// checks, so a construction bug yields `None`, never a wrong proof. An independent
/// checker (Carcara) accepts the same proof against the **inlined** `.smt2` problem
/// (no `define-fun` hoisting), `la_generic` over the opaque `(f args)` atoms.
///
/// Returns `None` when:
///
/// - the abstraction step fails or the abstracted conjunction is not `LRA`-`unsat`
///   (e.g. the refutation genuinely needs congruence — outside the congruence-free
///   slice this emitter targets) so [`prove_lra_unsat_alethe`] declines; or
/// - any fresh symbol cannot be translated back to its application term; or
/// - the assembled proof fails its own [`check_alethe_lra`] re-check.
#[must_use]
pub fn prove_uflra_unsat_alethe(
    arena: &mut TermArena,
    assertions: &[TermId],
) -> Option<Vec<AletheCommand>> {
    use axeyum_ir::{FuncId, SymbolId};

    // Congruence-free abstraction: each distinct `f(args)` → one fresh real var.
    let elim = axeyum_rewrite::eliminate_functions(arena, assertions).ok()?;
    let abstraction = elim.abstraction().to_vec();
    if abstraction.len() != assertions.len() {
        return None;
    }
    // `(fresh symbol, func, rewritten args)` for the back-substitution.
    let applications: Vec<(SymbolId, FuncId, Vec<TermId>)> = elim
        .applications()
        .into_iter()
        .map(|(func, args, fresh)| (fresh, func, args.to_vec()))
        .collect();

    // Refute the pure-LRA abstraction (fresh vars are ordinary reals here).
    let reduced_proof = prove_lra_unsat_alethe(arena, &abstraction)?;

    // Map each fresh symbol NAME → its opaque application `AletheTerm` (recursively,
    // since a nested `f(g(c))` abstracts `g(c)` to a fresh var inside `f`'s args).
    let fresh_to_app: BTreeMap<SymbolId, (FuncId, Vec<TermId>)> = applications
        .iter()
        .map(|(fresh, func, args)| (*fresh, (*func, args.clone())))
        .collect();
    let mut name_to_app: BTreeMap<String, AletheTerm> = BTreeMap::new();
    for &(fresh, _, _) in &applications {
        let (name, _sort) = arena.symbol(fresh);
        let name = name.to_owned();
        let app = fresh_symbol_to_alethe(arena, fresh, &fresh_to_app)?;
        name_to_app.insert(name, app);
    }

    // Substitute fresh-var `Const`s back to `(f args)` in every proof atom.
    let mut commands = reduced_proof;
    for command in &mut commands {
        match command {
            AletheCommand::Assume { clause, .. } | AletheCommand::Step { clause, .. } => {
                for lit in clause.iter_mut() {
                    substitute_apps(&mut lit.atom, &name_to_app);
                }
            }
        }
    }

    // Self-validate with the opaque-aware `la_generic` checker, then return.
    if matches!(check_alethe_lra(&commands), Ok(true)) {
        Some(commands)
    } else {
        None
    }
}

/// Integer analogue of [`prove_uflra_unsat_alethe`]: emits a checkable
/// `lia_generic` refutation for a congruence-free `QF_UFLIA` conjunction whose
/// contradiction is already present after replacing each arithmetic-sorted UF
/// application with one opaque integer variable.
#[must_use]
pub fn prove_uflia_opaque_unsat_alethe(
    arena: &mut TermArena,
    assertions: &[TermId],
) -> Option<Vec<AletheCommand>> {
    use axeyum_ir::{FuncId, SymbolId};

    let elim = axeyum_rewrite::eliminate_functions(arena, assertions).ok()?;
    let abstraction = elim.abstraction().to_vec();
    if abstraction.len() != assertions.len() {
        return None;
    }
    let applications: Vec<(SymbolId, FuncId, Vec<TermId>)> = elim
        .applications()
        .into_iter()
        .map(|(func, args, fresh)| (fresh, func, args.to_vec()))
        .collect();
    if applications.is_empty() {
        return None;
    }

    let reduced_proof = prove_lia_unsat_alethe(arena, &abstraction)?;

    let fresh_to_app: BTreeMap<SymbolId, (FuncId, Vec<TermId>)> = applications
        .iter()
        .map(|(fresh, func, args)| (*fresh, (*func, args.clone())))
        .collect();
    let mut name_to_app: BTreeMap<String, AletheTerm> = BTreeMap::new();
    for &(fresh, _, _) in &applications {
        let (name, _sort) = arena.symbol(fresh);
        let name = name.to_owned();
        let app = fresh_symbol_to_int_alethe(arena, fresh, &fresh_to_app)?;
        name_to_app.insert(name, app);
    }

    let mut commands = reduced_proof;
    for command in &mut commands {
        match command {
            AletheCommand::Assume { clause, .. } | AletheCommand::Step { clause, .. } => {
                for lit in clause.iter_mut() {
                    substitute_apps(&mut lit.atom, &name_to_app);
                }
            }
        }
    }

    if matches!(check_alethe_lra(&commands), Ok(true)) {
        Some(commands)
    } else {
        None
    }
}

/// Renders a fresh Ackermann symbol as its opaque application `AletheTerm`
/// `(funcname arg0 …)`, recursively expanding any argument that is itself a fresh
/// application symbol. `None` if a fresh symbol has no application entry.
fn fresh_symbol_to_alethe(
    arena: &TermArena,
    fresh: axeyum_ir::SymbolId,
    fresh_to_app: &BTreeMap<axeyum_ir::SymbolId, (axeyum_ir::FuncId, Vec<TermId>)>,
) -> Option<AletheTerm> {
    let (func, args) = fresh_to_app.get(&fresh)?;
    let (name, _params, _result) = arena.function(*func);
    let name = name.to_owned();
    let mut converted = Vec::with_capacity(args.len());
    for &arg in args {
        converted.push(app_arg_to_alethe(arena, arg, fresh_to_app)?);
    }
    Some(AletheTerm::App(name, converted))
}

/// Integer counterpart of [`fresh_symbol_to_alethe`].
fn fresh_symbol_to_int_alethe(
    arena: &TermArena,
    fresh: axeyum_ir::SymbolId,
    fresh_to_app: &BTreeMap<axeyum_ir::SymbolId, (axeyum_ir::FuncId, Vec<TermId>)>,
) -> Option<AletheTerm> {
    let (func, args) = fresh_to_app.get(&fresh)?;
    let (name, _params, _result) = arena.function(*func);
    let name = name.to_owned();
    let mut converted = Vec::with_capacity(args.len());
    for &arg in args {
        converted.push(app_arg_to_int_alethe(arena, arg, fresh_to_app)?);
    }
    Some(AletheTerm::App(name, converted))
}

/// Renders an application **argument** (a rewritten/abstracted term) as an
/// `AletheTerm`: a fresh application symbol expands to its `(f …)` form, any other
/// linear-real term goes through [`real_subterm_to_alethe`]. `None` outside that.
fn app_arg_to_alethe(
    arena: &TermArena,
    arg: TermId,
    fresh_to_app: &BTreeMap<axeyum_ir::SymbolId, (axeyum_ir::FuncId, Vec<TermId>)>,
) -> Option<AletheTerm> {
    if let TermNode::Symbol(symbol) = arena.node(arg)
        && fresh_to_app.contains_key(symbol)
    {
        return fresh_symbol_to_alethe(arena, *symbol, fresh_to_app);
    }
    real_subterm_to_alethe(arena, arg)
}

/// Integer counterpart of [`app_arg_to_alethe`].
fn app_arg_to_int_alethe(
    arena: &TermArena,
    arg: TermId,
    fresh_to_app: &BTreeMap<axeyum_ir::SymbolId, (axeyum_ir::FuncId, Vec<TermId>)>,
) -> Option<AletheTerm> {
    if let TermNode::Symbol(symbol) = arena.node(arg)
        && fresh_to_app.contains_key(symbol)
    {
        return fresh_symbol_to_int_alethe(arena, *symbol, fresh_to_app);
    }
    int_subterm_to_alethe(arena, arg)
}

/// Substitutes each fresh-variable `Const(name)` whose `name` is a known abstraction
/// symbol with its opaque application `AletheTerm`, in place and recursively.
fn substitute_apps(term: &mut AletheTerm, name_to_app: &BTreeMap<String, AletheTerm>) {
    match term {
        AletheTerm::Const(name) => {
            if let Some(app) = name_to_app.get(name) {
                *term = app.clone();
            }
        }
        AletheTerm::App(_, args) | AletheTerm::Indexed { args, .. } => {
            for arg in args.iter_mut() {
                substitute_apps(arg, name_to_app);
            }
        }
    }
}

/// Computes the per-literal Farkas `:args` for the `la_generic` step over
/// `assertions`, in assertion (= clause-literal) order — **one coefficient per
/// assertion**.
///
/// The atom-level multipliers come from [`crate::lra::lra_farkas_certificate`];
/// `certificate.origins[i]` names the assertion that atom `i` came from. We group
/// the atoms by origin and reduce each assertion's atoms to its single `la_generic`
/// coefficient:
///
/// - An **inequality** assertion contributes exactly one atom; its coefficient is
///   that atom's (nonnegative) multiplier — byte-identical to the prior
///   inequality-only output.
/// - An **equality** `a = b` splits into two atoms in push order: `+(a − b) ≤ 0`
///   with multiplier `m0` and `−(a − b) ≤ 0` with multiplier `m1`. Carcara negates
///   the clause literal `(not (= a b))` to `(= a b)` and forms `a − b` with the
///   coefficient applied **signed** (`match op { Equals => a, _ => a.abs() }`),
///   unlike inequality literals which it negate-flips and takes `abs` of. The
///   matching coefficient is therefore the signed `c = m1 − m0` (see the inline
///   note at the equality arm for why; confirmed against the Carcara binary —
///   `(1, 1, 1)` validates the mixed `x = 1 ∧ x + y ≤ 0 ∧ y ≥ 1`). `c` may be
///   negative or zero. We confirm the two atoms are genuine negatives of each other
///   (the equality-split structural invariant) before using order to pick `+diff`,
///   so a future reordering cannot silently flip the sign.
/// - **More than two atoms** for one assertion (e.g. an unsupported conjunction we
///   cannot soundly reduce to one coefficient): we cannot align it to a single
///   coefficient, so we fall back to emitting **no args** for the whole step (the
///   prior behavior).
///
/// Carcara re-derives the contradiction from these coefficients, so a wrong
/// coefficient is caught externally — never trusted.
///
/// Returns an empty vector when the certificate is absent (not unsat through the
/// Farkas path), when any assertion has an unexpected atom shape, or when any
/// coefficient cannot be rendered.
fn farkas_args(arena: &TermArena, assertions: &[TermId]) -> Vec<AletheTerm> {
    let Ok(Some(certificate)) = crate::lra::lra_farkas_certificate(arena, assertions) else {
        return Vec::new();
    };
    let mut args = Vec::with_capacity(assertions.len());
    for j in 0..assertions.len() {
        // The atoms (with their multipliers) that this assertion produced, in atom
        // (= push) order. Determinism: origins are in atom order already.
        let group: Vec<(&crate::lra::FarkasAtom, &Rational)> = certificate
            .origins
            .iter()
            .zip(certificate.atoms.iter().zip(&certificate.multipliers))
            .filter(|&(&origin, _)| origin == j)
            .map(|(_, atom_mult)| atom_mult)
            .collect();
        match group.as_slice() {
            // Inequality: the single atom's multiplier is the coefficient (always
            // nonnegative here — identical to the prior inequality-only output).
            [(_, m)] => match rational_to_alethe(m) {
                Some(term) => args.push(term),
                // Overflow rendering the coefficient ⇒ emit no args at all.
                None => return Vec::new(),
            },
            // Equality `a = b`: atoms are `+(a − b)` (mult `m0`) then `−(a − b)`
            // (mult `m1`) in push order. Confirm they are exact negatives (the
            // split invariant) before trusting order, then emit the signed
            // `c = m1 − m0`.
            //
            // Why `m1 − m0` (not `m0 − m1`)? Carcara forms `c · (a − b)` for an `=`
            // literal with the coefficient applied **signed** (no negate-flip),
            // whereas it negate-flips every inequality literal and takes
            // `coeff.abs()`. Our Farkas certificate's per-atom signs are the global
            // negation of Carcara's per-literal signs, so to keep all variables
            // cancelling, the equality coefficient must be `m1 − m0` (the negation
            // of the certificate's net `(m0 − m1) · (a − b)`). Confirmed against the
            // Carcara binary on the mixed equality/inequality case `x = 1 ∧
            // x + y ≤ 0 ∧ y ≥ 1`, which `m1 − m0` validates and `m0 − m1` rejects.
            [(atom0, m0), (atom1, m1)] => {
                if !is_negation_of(atom0, atom1) {
                    return Vec::new();
                }
                // An `i128` overflow forming the signed coefficient `m1 − m0` ⇒
                // emit no args at all (Carcara then reports `invalid`; our own
                // checker still re-derives the contradiction). Never a wrong proof.
                let Some(coeff) = (**m1).checked_sub(**m0) else {
                    return Vec::new();
                };
                match rational_to_alethe(&coeff) {
                    Some(term) => args.push(term),
                    None => return Vec::new(),
                }
            }
            // No atoms (assertion did not reach the certificate) or more than two
            // (a shape we cannot reduce to one coefficient): emit no args at all.
            _ => return Vec::new(),
        }
    }
    args
}

/// Whether `b` is the exact negation of `a`: every variable coefficient and the
/// constant are sign-flipped, with the same strictness. This is the structural
/// invariant of the equality split `a = b ↦ {+(a − b) ≤ 0, −(a − b) ≤ 0}`; we
/// check it so the order-based `+diff`-first assumption is guarded rather than
/// blindly trusted.
fn is_negation_of(a: &crate::lra::FarkasAtom, b: &crate::lra::FarkasAtom) -> bool {
    if a.strict != b.strict {
        return false;
    }
    // An `i128` overflow negating `b.constant` ⇒ cannot confirm the negation
    // invariant ⇒ treat as "not a negation" (the caller then emits no args).
    let Some(neg_b_const) = b.constant.checked_neg() else {
        return false;
    };
    if a.constant != neg_b_const {
        return false;
    }
    if a.coeffs.len() != b.coeffs.len() {
        return false;
    }
    a.coeffs
        .iter()
        .zip(&b.coeffs)
        .all(|(&(ia, ca), &(ib, cb))| ia == ib && cb.checked_neg() == Some(ca))
}

/// Renders a (possibly signed) Farkas coefficient as an Alethe `:args` term in the
/// form Carcara's `la_generic` accepts:
///
/// - a nonnegative integer `n` as the bare numeral `Const("n")`;
/// - a negative integer `-n` as the unary application `(- n)`;
/// - a nonnegative proper fraction `p/q` (`q != 1`) as `(/ p.0 q.0)` (Real-typed
///   numerals, so the division re-parses as `Real`);
/// - a negative fraction `-(p/q)` as `(- (/ p.0 q.0))`.
///
/// Inequality multipliers are nonnegative, so for those this is identical to the
/// prior renderer; equality coefficients (`m0 − m1`) may be negative or zero, hence
/// the sign handling. All four forms were confirmed accepted by the Carcara binary.
///
/// Returns `None` only when taking the magnitude of a negative coefficient
/// overflows `i128` (i.e. `i128::MIN`); the caller then emits no `:args` (a sound
/// degradation — the proof's own checker still re-derives the contradiction).
fn rational_to_alethe(value: &Rational) -> Option<AletheTerm> {
    // `value < 0` compared to zero — never overflows.
    let negative = *value < Rational::zero();
    let magnitude = if negative {
        value.checked_neg()?
    } else {
        *value
    };
    let num = magnitude.numerator();
    let den = magnitude.denominator();
    let positive_term = if den == 1 {
        AletheTerm::Const(num.to_string())
    } else {
        AletheTerm::App(
            "/".to_owned(),
            vec![
                AletheTerm::Const(format!("{num}.0")),
                AletheTerm::Const(format!("{den}.0")),
            ],
        )
    };
    Some(if negative {
        AletheTerm::App("-".to_owned(), vec![positive_term])
    } else {
        positive_term
    })
}

/// Converts an IR linear-real **comparison atom** to its Alethe term, or `None` if
/// it is not a recognised comparison over linear real operands.
fn real_atom_to_alethe(arena: &TermArena, t: TermId) -> Option<AletheTerm> {
    let TermNode::App { op, args } = arena.node(t) else {
        return None;
    };
    if args.len() != 2 {
        return None;
    }
    let head = match op {
        Op::RealLe => "<=",
        Op::RealLt => "<",
        Op::RealGe => ">=",
        Op::RealGt => ">",
        Op::Eq => "=",
        _ => return None,
    };
    let a = real_subterm_to_alethe(arena, args[0])?;
    let b = real_subterm_to_alethe(arena, args[1])?;
    Some(AletheTerm::App(head.to_owned(), vec![a, b]))
}

/// Converts an IR linear-real term to its Alethe term (the inverse of
/// [`real_term`]): symbols → `Const(name)`, constants → `Const("p/q")`, and the
/// linear operators `+`/`-`/`*` to their SMT-LIB heads. `None` outside that
/// fragment.
fn real_subterm_to_alethe(arena: &TermArena, t: TermId) -> Option<AletheTerm> {
    match arena.node(t) {
        TermNode::Symbol(s) => {
            let (name, _sort) = arena.symbol(*s);
            Some(AletheTerm::Const(name.to_owned()))
        }
        TermNode::RealConst(r) => Some(AletheTerm::Const(format!(
            "{}/{}",
            r.numerator(),
            r.denominator()
        ))),
        TermNode::App { op, args } => {
            let head = match op {
                Op::RealAdd => "+",
                Op::RealSub | Op::RealNeg => "-",
                Op::RealMul => "*",
                _ => return None,
            };
            let mut converted = Vec::with_capacity(args.len());
            for &arg in args {
                converted.push(real_subterm_to_alethe(arena, arg)?);
            }
            Some(AletheTerm::App(head.to_owned(), converted))
        }
        _ => None,
    }
}

/// Emits a checkable Alethe refutation of an `unsat` linear-**integer**-arithmetic
/// conjunction `assertions`, or `None` if they are not `unsat` (by
/// [`check_with_lia_simplex`]) or any atom is outside the linear-integer fragment
/// the term converter covers.
///
/// The proof assumes each atom `φᵢ`, derives the tautology clause
/// `(cl ¬φ1 … ¬φn)` by **`lia_generic`** (valid because `⋀ φᵢ` is integer-`unsat`),
/// and resolves it against the assumes to the empty clause. It is **self-validated**
/// through [`check_alethe_lra`] and returned only if it checks — so a construction
/// bug yields `None`, never a wrong proof. This is the emission counterpart to the
/// `lia_generic` checker (the integer dual of [`prove_lra_unsat_alethe`]).
#[must_use]
pub fn prove_lia_unsat_alethe(
    arena: &TermArena,
    assertions: &[TermId],
) -> Option<Vec<AletheCommand>> {
    // Only a genuine LIA refutation has a proof.
    if !matches!(
        check_with_lia_simplex(arena, assertions),
        Ok(CheckResult::Unsat)
    ) {
        return None;
    }
    // Convert each atom to an Alethe comparison; bail if any is outside the fragment.
    let atoms: Vec<AletheTerm> = assertions
        .iter()
        .map(|&a| int_atom_to_alethe(arena, a))
        .collect::<Option<Vec<_>>>()?;
    if atoms.is_empty() {
        return None;
    }

    let mut commands = Vec::with_capacity(atoms.len() + 2);
    let mut premise_ids: Vec<String> = Vec::with_capacity(atoms.len());
    // Assume each atom `φᵢ` as the unit clause `(cl φᵢ)`.
    for (i, atom) in atoms.iter().enumerate() {
        let id = format!("h{i}");
        commands.push(AletheCommand::Assume {
            id: id.clone(),
            clause: vec![AletheLit {
                atom: atom.clone(),
                negated: false,
            }],
        });
        premise_ids.push(id);
    }
    // `lia_generic` derives `(cl ¬φ1 … ¬φn)` — valid since `⋀ φᵢ` is integer-unsat.
    let lia_clause: Vec<AletheLit> = atoms
        .iter()
        .map(|atom| AletheLit {
            atom: atom.clone(),
            negated: true,
        })
        .collect();
    commands.push(AletheCommand::Step {
        id: "lia".to_owned(),
        clause: lia_clause,
        rule: "lia_generic".to_owned(),
        premises: Vec::new(),
        args: Vec::new(),
    });
    // Resolve the lia_generic clause against every assume to the empty clause.
    let mut resolution_premises = vec!["lia".to_owned()];
    resolution_premises.extend(premise_ids);
    commands.push(AletheCommand::Step {
        id: "empty".to_owned(),
        clause: Vec::new(),
        rule: "resolution".to_owned(),
        premises: resolution_premises,
        args: Vec::new(),
    });

    // Self-validate: return the proof only if it checks (and derives `(cl)`).
    if matches!(check_alethe_lra(&commands), Ok(true)) {
        Some(commands)
    } else {
        None
    }
}

/// Crate-internal accessor for [`int_atom_to_alethe`]: lets the finite-quantifier
/// certificate emitter ([`crate::quant_finite_cert`]) translate a bare integer
/// comparison instance to the **same** Alethe atom shape the `lia_generic` ground
/// tail produces, so the spliced instance literals key-match exactly.
pub(crate) fn int_atom_to_alethe_pub(arena: &TermArena, t: TermId) -> Option<AletheTerm> {
    int_atom_to_alethe(arena, t)
}

/// Crate-internal accessor for [`real_atom_to_alethe`]: lets mixed-theory
/// certificate builders recognize Boolean-structured real-arithmetic residuals
/// without duplicating the renderer's fragment test.
pub(crate) fn real_atom_to_alethe_pub(arena: &TermArena, t: TermId) -> Option<AletheTerm> {
    real_atom_to_alethe(arena, t)
}

/// Integer counterpart of [`real_atom_to_alethe`]: converts an IR linear-integer
/// **comparison atom** to its Alethe term, or `None` if it is not a recognised
/// comparison over linear integer operands.
fn int_atom_to_alethe(arena: &TermArena, t: TermId) -> Option<AletheTerm> {
    let TermNode::App { op, args } = arena.node(t) else {
        return None;
    };
    if args.len() != 2 {
        return None;
    }
    let head = match op {
        Op::IntLe => "<=",
        Op::IntLt => "<",
        Op::IntGe => ">=",
        Op::IntGt => ">",
        Op::Eq => "=",
        _ => return None,
    };
    let a = int_subterm_to_alethe(arena, args[0])?;
    let b = int_subterm_to_alethe(arena, args[1])?;
    Some(AletheTerm::App(head.to_owned(), vec![a, b]))
}

/// Integer counterpart of [`real_subterm_to_alethe`]: converts an IR linear-integer
/// term to its Alethe term (the inverse of [`int_term`]): symbols → `Const(name)`,
/// constants → `Const(n)` (a plain integer string), and the linear operators
/// `+`/`-`/`*` to their SMT-LIB heads. `None` outside that fragment.
fn int_subterm_to_alethe(arena: &TermArena, t: TermId) -> Option<AletheTerm> {
    match arena.node(t) {
        TermNode::Symbol(s) => {
            let (name, _sort) = arena.symbol(*s);
            Some(AletheTerm::Const(name.to_owned()))
        }
        TermNode::IntConst(n) => Some(AletheTerm::Const(n.to_string())),
        TermNode::App { op, args } => {
            let head = match op {
                Op::IntAdd => "+",
                Op::IntSub | Op::IntNeg => "-",
                Op::IntMul => "*",
                _ => return None,
            };
            let mut converted = Vec::with_capacity(args.len());
            for &arg in args {
                converted.push(int_subterm_to_alethe(arena, arg)?);
            }
            Some(AletheTerm::App(head.to_owned(), converted))
        }
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::{
        check_alethe_lra, prove_lia_unsat_alethe, prove_lra_unsat_alethe,
        prove_uflia_opaque_unsat_alethe,
    };
    use axeyum_cnf::{AletheCommand, AletheError, AletheLit, AletheTerm};
    use axeyum_ir::{Rational, Sort, TermArena};

    #[test]
    fn emits_checkable_lra_refutation() {
        // x ≤ 0 ∧ 1 ≤ x is unsat; the emitter produces an la_generic proof that
        // re-checks (Ok(true), derives the empty clause).
        let mut arena = TermArena::new();
        let x = arena.real_var("x").unwrap();
        let zero = arena.real_const(Rational::integer(0));
        let one = arena.real_const(Rational::integer(1));
        let a1 = arena.real_le(x, zero).unwrap();
        let a2 = arena.real_le(one, x).unwrap();
        let proof = prove_lra_unsat_alethe(&arena, &[a1, a2]).expect("emits an LRA proof");
        assert_eq!(check_alethe_lra(&proof), Ok(true));
    }

    #[test]
    fn emits_checkable_lra_refutation_with_coefficients() {
        // 2x ≤ -1 ∧ x ≥ 0 is unsat (x ≥ 0 ⇒ 2x ≥ 0 > -1); exercises a non-trivial
        // linear combination + a negative numeral in the emitted terms.
        let mut arena = TermArena::new();
        let x = arena.real_var("x").unwrap();
        let two = arena.real_const(Rational::integer(2));
        let neg_one = arena.real_const(Rational::integer(-1));
        let zero = arena.real_const(Rational::integer(0));
        let two_x = arena.real_mul(two, x).unwrap();
        let a1 = arena.real_le(two_x, neg_one).unwrap();
        let a2 = arena.real_ge(x, zero).unwrap();
        let proof = prove_lra_unsat_alethe(&arena, &[a1, a2]).expect("emits an LRA proof");
        assert_eq!(check_alethe_lra(&proof), Ok(true));
    }

    #[test]
    fn no_proof_for_satisfiable_lra() {
        // x ≤ 5 is satisfiable — no refutation.
        let mut arena = TermArena::new();
        let x = arena.real_var("x").unwrap();
        let five = arena.real_const(Rational::integer(5));
        let a = arena.real_le(x, five).unwrap();
        assert!(prove_lra_unsat_alethe(&arena, &[a]).is_none());
    }

    #[test]
    fn emits_checkable_congruence_free_uflia_refutation() {
        // f(0) <= 0 ∧ f(0) >= 1 is unsat over integer-valued f, and the proof
        // needs no functional-consistency lemma: the same application is one
        // opaque integer variable in the `lia_generic` check.
        let mut arena = TermArena::new();
        let f = arena.declare_fun("f", &[Sort::Int], Sort::Int).unwrap();
        let zero = arena.int_const(0);
        let one = arena.int_const(1);
        let f0 = arena.apply(f, &[zero]).unwrap();
        let a1 = arena.int_le(f0, zero).unwrap();
        let a2 = arena.int_ge(f0, one).unwrap();
        let proof = prove_uflia_opaque_unsat_alethe(&mut arena, &[a1, a2])
            .expect("emits congruence-free UFLIA proof");
        assert_eq!(check_alethe_lra(&proof), Ok(true));
    }

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
            args: Vec::new(),
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

    #[test]
    fn lia_generic_accepts_integer_only_tautology() {
        // (cl (<= x 0) (>= x 1)) is valid over Int: its negation
        // ¬(<= x 0) = (x > 0) = (x >= 1) and ¬(>= x 1) = (x < 1) = (x <= 0); the
        // conjunction x >= 1 ∧ x <= 0 has no integer solution ⇒ integer-UNSAT ⇒
        // the clause is a tautology over Int. The lone lia_generic step verifies
        // (no empty clause) ⇒ Ok(false), i.e. checked, not refuted.
        let clause = vec![cmp("<=", var("x"), num("0")), cmp(">=", var("x"), num("1"))];
        let proof = vec![step("t1", clause.clone(), "lia_generic", &[])];
        assert_eq!(
            check_alethe_lra(&proof),
            Ok(false),
            "an integer-only tautology must be accepted by lia_generic"
        );

        // The SAME clause under la_generic is REJECTED: over the reals it is not
        // valid (x = 0.5 falsifies both disjuncts), so its real negation is SAT.
        let real_proof = vec![step("t1", clause, "la_generic", &[])];
        assert_eq!(
            check_alethe_lra(&real_proof),
            Err(AletheError::StepNotEntailed {
                id: "t1".to_owned()
            }),
            "the same clause is NOT real-valid (x = 0.5) ⇒ la_generic must reject it"
        );
    }

    #[test]
    fn lia_generic_accepts_opaque_integer_app_tautology() {
        // The opaque term `(f 0)` is treated as one arbitrary integer variable.
        // Thus `f(0) <= 0 ∨ f(0) >= 1` is an integer-valid gap tautology.
        let f0 = AletheTerm::App("f".to_owned(), vec![num("0")]);
        let clause = vec![cmp("<=", f0.clone(), num("0")), cmp(">=", f0, num("1"))];
        let proof = vec![step("t1", clause, "lia_generic", &[])];
        assert_eq!(check_alethe_lra(&proof), Ok(false));
    }

    #[test]
    fn lia_generic_rejects_non_tautology() {
        // (cl (<= x 0) (>= x 2)) is NOT valid even over Int: its negation
        // (x > 0) ∧ (x < 2) has the integer solution x = 1 ⇒ SAT ⇒ not a
        // tautology ⇒ the step must be rejected as not entailed.
        let clause = vec![cmp("<=", var("x"), num("0")), cmp(">=", var("x"), num("2"))];
        let proof = vec![step("t1", clause, "lia_generic", &[])];
        assert_eq!(
            check_alethe_lra(&proof),
            Err(AletheError::StepNotEntailed {
                id: "t1".to_owned()
            }),
            "a non-tautology (x = 1 satisfies the negation) must be REJECTED"
        );
    }

    #[test]
    fn emits_checkable_lia_refutation() {
        // x ≤ 0 ∧ x ≥ 1 is integer-unsat; the emitter produces a lia_generic proof
        // that re-checks (Ok(true), derives the empty clause).
        let mut arena = TermArena::new();
        let x = arena.int_var("x").unwrap();
        let zero = arena.int_const(0);
        let one = arena.int_const(1);
        let a1 = arena.int_le(x, zero).unwrap();
        let a2 = arena.int_ge(x, one).unwrap();
        let proof = prove_lia_unsat_alethe(&arena, &[a1, a2]).expect("emits an LIA proof");
        assert_eq!(check_alethe_lra(&proof), Ok(true));
    }

    #[test]
    fn no_lia_proof_for_satisfiable() {
        // x ≥ 0 is satisfiable — no refutation.
        let mut arena = TermArena::new();
        let x = arena.int_var("x").unwrap();
        let zero = arena.int_const(0);
        let a = arena.int_ge(x, zero).unwrap();
        assert!(prove_lia_unsat_alethe(&arena, &[a]).is_none());
    }
}
