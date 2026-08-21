//! Multi-term Handelman / Positivstellensatz refutations for `QF_NRA`.
//!
//! # The shape
//!
//! [`crate::nra_product_cert`] certifies the refutations that are ONE product of
//! two hypotheses. It deliberately declines the ones that need a *combination*,
//! and those are the interesting corpus rows:
//!
//! ```text
//! cli__regress1__nl__coeff-unsat.smt2
//!   a > 0, b > 0, a >= 3b, a² < 8b²
//!   -- (a−3b)·a + 3(a−3b)·b + (8b² − a²) + b·b  ==  0, and the sum is > 0
//!
//! cli__regress1__nl__combine.smt2
//!   c > 1, ab > 1, abc < 1
//!   -- (c−1)(ab−1) + (1 − abc) + (ab−1) + (c−1)  ==  0, and the sum is > 0
//!
//! cli__regress1__nl__approx-sqrt-unsat.smt2
//!   x² = 2, x > 0, and a three-way disjunction of quadratic lower bounds
//!   -- one combination PER DISJUNCT, each using the equality x² − 2 = 0 with a
//!      degree-1 polynomial multiplier
//! ```
//!
//! All three shipped as bare `Evidence::Unsat(None)`.
//!
//! # The certificate
//!
//! Per case: a set of atoms the query asserts, a list of **products** of those
//! atoms with positive rational coefficients, a list of **equality atoms with
//! polynomial multipliers**, and a residual constant. The claim is
//!
//! ```text
//! Σ λ_t · Π_{i ∈ factors(t)} Q_i   +   Σ_j q_j · E_j   ≡   residual
//! ```
//!
//! as polynomials, where every `Q_i ≥ 0` and every `E_j = 0` under the query's
//! own assertions. The left side is then `≥ 0`, so a `residual < 0` is a
//! contradiction — and a `residual = 0` is one too, but ONLY when some product
//! with a positive coefficient is strictly positive.
//!
//! # Strictness is the soundness argument, again
//!
//! `p ≥ 0` and `q ≥ 0` give `pq ≥ 0`. A sum of such products is `≥ 0`, which
//! contradicts `= −1` but NOT `= 0`. It contradicts `= 0` only if one term is
//! strictly positive, which needs *every* factor of that term strict. Get this
//! backwards and the module certifies satisfiable queries: `x ≥ 0`, `y ≥ 0`,
//! `xy ≤ 0` has the combination `1·(x·y) + 1·(−xy) ≡ 0` and is satisfiable at
//! `x = 0`. So each atom's strictness is carried and re-derived, and the rule
//! lives in exactly one function, [`residual_refutes`].
//!
//! # Relaxations, and why a certificate may weaken its own hypotheses
//!
//! `Rational` is an `i128` fraction. `approx-sqrt-unsat`'s third disjunct has
//! the constant `2.0000000000000000000000000001` — denominator `10^28` — and the
//! *tight* refutation needs `(2+k)²`, whose numerator is `1.6·10^57`. No exact
//! `i128` derivation of that refutation exists, and an approximate one is not a
//! certificate.
//!
//! So an atom may carry a **relaxation** `r ≥ 0`: the derivation uses
//! `Q_i = nonneg_form(atom_i) + r_i` instead of `nonneg_form(atom_i)`. That is
//! still implied by the atom (a nonnegative quantity plus a nonnegative constant
//! is nonnegative), it is still a lower bound the query genuinely licenses, and
//! rounding `2.0000000000000000000000000001` up to `2.000000000001` brings every
//! product back inside `i128` with room to spare. The relaxation is carried, so
//! the checker re-derives the weakened hypothesis rather than trusting it.
//!
//! # What the producer and the checker do NOT share
//!
//! The producer finds the coefficients with an LP: it abstracts every monomial
//! to a fresh real variable, hands the resulting linear system to the exact
//! Fourier–Motzkin/Farkas engine in [`crate::lra`], and reads the multipliers
//! back. The checker never runs an LP. It re-parses the original assertions,
//! binds each carried atom to something the query literally says, multiplies the
//! polynomials out with exact rational arithmetic, and applies
//! [`residual_refutes`]. Producer and checker can therefore disagree — which is
//! the point, and is why this is not `fresh == certificate`.

use std::collections::BTreeMap;

use axeyum_ir::{Op, Rational, TermArena, TermId, TermNode};

use crate::nra_product_cert::{AtomSign, Mono, NamedPoly, atom_or_equality, from_wire};
use crate::term_walk::flatten_op_spine;

/// A rational in wire form: `(numerator, denominator)`.
type WireRat = (i128, i128);

/// A polynomial in wire form: `[(monomial, numerator, denominator)]`.
type WirePoly = Vec<(Mono, i128, i128)>;

/// Largest number of distinct monomials the monomial abstraction will build.
/// Fourier–Motzkin is doubly exponential in the variable count, so this is a
/// budget, not a semantic limit.
const MAX_MONOMIALS: usize = 16;

/// Largest number of generators (atoms, products, equality multiples) handed to
/// the LP.
const MAX_GENERATORS: usize = 48;

/// A constant-term denominator above this makes an atom a relaxation candidate.
const RELAXATION_DENOMINATOR_THRESHOLD: i128 = 1_000_000_000_000;

/// Decimal grids the producer will round a huge-denominator constant term up to,
/// coarsest first.
const RELAXATION_GRIDS: [u32; 5] = [6, 9, 12, 15, 18];

/// One hypothesis the refutation uses: a polynomial compared to zero, exactly as
/// the query states it, plus a nonnegative slack the derivation is allowed to
/// add to its nonnegative form.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HandelmanAtom {
    /// The polynomial, keyed on SOURCE NAMES (never `SymbolId`: ids are
    /// arena-local and mean nothing against the fresh parse re-validation uses).
    poly: WirePoly,
    /// How the query compares that polynomial to zero.
    sign: AtomSign,
    /// A nonnegative constant added to the atom's nonnegative form before use.
    /// Zero for almost every atom; see the module docs for the one shape that
    /// needs it.
    relaxation: WireRat,
}

impl HandelmanAtom {
    /// The asserted sign of this atom.
    #[must_use]
    pub const fn sign(&self) -> AtomSign {
        self.sign
    }

    /// The relaxation added to this atom's nonnegative form, as
    /// `(numerator, denominator)`.
    #[must_use]
    pub const fn relaxation(&self) -> WireRat {
        self.relaxation
    }
}

/// One product term: a positive rational coefficient times a product of atoms.
/// An empty `factors` is the empty product, i.e. the constant `1`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HandelmanProduct {
    coefficient: WireRat,
    factors: Vec<usize>,
}

impl HandelmanProduct {
    /// The coefficient, as `(numerator, denominator)`. Must be positive.
    #[must_use]
    pub const fn coefficient(&self) -> WireRat {
        self.coefficient
    }

    /// Indices into the case's atom list, with multiplicity.
    #[must_use]
    pub fn factors(&self) -> &[usize] {
        &self.factors
    }
}

/// One case of the refutation. A conjunctive query has exactly one; a query
/// refuted by splitting a top-level disjunction has one per disjunct.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HandelmanCase {
    /// The hypotheses this case uses.
    atoms: Vec<HandelmanAtom>,
    /// Index into `atoms` of the atom that is this case's disjunct, when the
    /// refutation splits. `None` for a purely conjunctive refutation.
    case_atom: Option<usize>,
    /// Product terms with positive coefficients.
    products: Vec<HandelmanProduct>,
    /// The multiplier polynomial, and the index of the [`AtomSign::Zero`] atom
    /// it multiplies. The multiplier's sign is free: an equality contributes
    /// zero whatever it is multiplied by.
    equalities: Vec<(WirePoly, usize)>,
    /// The constant the whole combination must equal.
    residual: WireRat,
}

impl HandelmanCase {
    /// The hypotheses this case uses.
    #[must_use]
    pub fn atoms(&self) -> &[HandelmanAtom] {
        &self.atoms
    }

    /// The product terms.
    #[must_use]
    pub fn products(&self) -> &[HandelmanProduct] {
        &self.products
    }

    /// The residual constant, as `(numerator, denominator)`.
    #[must_use]
    pub const fn residual(&self) -> WireRat {
        self.residual
    }

    /// The index of this case's disjunct, when the refutation splits.
    #[must_use]
    pub const fn case_atom(&self) -> Option<usize> {
        self.case_atom
    }
}

/// A multi-term Handelman refutation: one combination per case, and (when there
/// is more than one case) the cases exhaust a disjunction the query asserts.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HandelmanRefutationCertificate {
    cases: Vec<HandelmanCase>,
}

impl HandelmanRefutationCertificate {
    /// The cases, one per disjunct when the refutation splits.
    #[must_use]
    pub fn cases(&self) -> &[HandelmanCase] {
        &self.cases
    }

    /// Whether this refutation splits a top-level disjunction.
    #[must_use]
    pub fn is_case_split(&self) -> bool {
        self.cases.len() > 1
    }
}

/// **The soundness rule, stated once.**
///
/// The combination's left side is a sum of nonnegative products (the equality
/// terms contribute exactly zero), so it is `≥ 0`, and `> 0` when some product
/// with a positive coefficient has every factor strict. A `residual` of `−1`
/// therefore contradicts either way; a residual of `0` contradicts only the
/// strict case; a positive residual contradicts nothing at all.
///
/// `None` means an `i128` overflow made the comparison impossible, which never
/// licenses an `unsat`.
fn residual_refutes(residual: Rational, has_strict_product: bool) -> Option<bool> {
    use core::cmp::Ordering;
    match residual.checked_cmp(&Rational::zero())? {
        Ordering::Less => Some(true),
        Ordering::Equal => Some(has_strict_product),
        Ordering::Greater => Some(false),
    }
}

/// The nonnegative form of an atom, plus its relaxation: the polynomial `Q` with
/// `Q ≥ 0` (or `Q > 0`) under the atom, and whether that holds strictly.
///
/// `p < 0` and `p ≤ 0` are flipped to `−p`; an equality has no nonnegative form
/// and returns `None`, which is what stops an equality being used as a product
/// factor (`e = 0` gives `e·e ≥ 0` but also `e·f = 0`, and the combination rules
/// below are stated for genuine lower bounds only).
fn nonnegative_form(
    poly: &NamedPoly,
    sign: AtomSign,
    relaxation: Rational,
) -> Option<(NamedPoly, bool)> {
    let (base, strict) = match sign {
        AtomSign::Positive => (poly.clone(), true),
        AtomSign::Nonnegative => (poly.clone(), false),
        AtomSign::Negative => (poly.neg()?, true),
        AtomSign::Nonpositive => (poly.neg()?, false),
        AtomSign::Zero => return None,
    };
    if relaxation.checked_cmp(&Rational::zero())? == core::cmp::Ordering::Less {
        return None;
    }
    Some((base.add(&NamedPoly::constant(relaxation))?, strict))
}

/// The top-level conjuncts of `assertions`.
///
/// `flatten_op_spine` rather than the binary-only collector the sibling modules
/// use: a 3-argument `and` or `or` is a LEAF to an arity-2 collector, and this
/// module's corpus target is a 3-way disjunction.
fn top_conjuncts(arena: &TermArena, assertions: &[TermId]) -> Vec<TermId> {
    let mut conjuncts = Vec::new();
    for &assertion in assertions {
        flatten_op_spine(arena, assertion, &mut conjuncts, Op::BoolAnd);
    }
    conjuncts
}

/// The atoms of every top-level conjunct of `assertions`.
fn query_atoms(arena: &TermArena, assertions: &[TermId]) -> Vec<(NamedPoly, AtomSign)> {
    top_conjuncts(arena, assertions)
        .iter()
        .filter_map(|&c| atom_or_equality(arena, c))
        .collect()
}

/// Every top-level conjunct that is a disjunction of atoms, as its disjunct
/// list. A disjunction with even one arm that is not an atom is skipped: a
/// partially covered case split proves nothing.
fn query_disjunctions(arena: &TermArena, assertions: &[TermId]) -> Vec<Vec<(NamedPoly, AtomSign)>> {
    let mut out = Vec::new();
    for conjunct in top_conjuncts(arena, assertions) {
        if !matches!(arena.node(conjunct), TermNode::App { op: Op::BoolOr, .. }) {
            continue;
        }
        let mut disjuncts = Vec::new();
        flatten_op_spine(arena, conjunct, &mut disjuncts, Op::BoolOr);
        if disjuncts.is_empty() {
            continue;
        }
        let arms: Option<Vec<(NamedPoly, AtomSign)>> = disjuncts
            .iter()
            .map(|&arm| atom_or_equality(arena, arm))
            .collect();
        if let Some(arms) = arms {
            out.push(arms);
        }
    }
    out
}

/// Rebuild `(numerator, denominator)`, rejecting a zero denominator (which
/// `Rational` never emits but a forged certificate can contain).
fn wire_rational(wire: WireRat) -> Option<Rational> {
    if wire.1 == 0 {
        return None;
    }
    Rational::checked_new(wire.0, wire.1)
}

/// Independently re-validate a certificate against the **original** assertions.
///
/// Two stages, deliberately separate:
///
/// 1. **Bind.** Every atom the certificate carries is something this query
///    literally asserts — or, for a case's designated atom, is that case's
///    disjunct of a disjunction the query asserts, with the cases exhausting it.
/// 2. **Re-derive.** The carried coefficients are multiplied out with exact
///    rational arithmetic; the sum must collapse to the carried residual, and
///    `residual_refutes` must close.
///
/// The checker runs no LP and reuses none of the producer's search, so it can
/// disagree with the producer rather than only with a different query.
#[must_use]
pub fn check_handelman_refutation(
    arena: &TermArena,
    assertions: &[TermId],
    certificate: &HandelmanRefutationCertificate,
) -> bool {
    let asserted = query_atoms(arena, assertions);

    if certificate.cases.len() == 1 && certificate.cases[0].case_atom.is_none() {
        return check_case(&certificate.cases[0], &asserted, None);
    }

    // A split refutation must cover EVERY arm of one disjunction the query
    // asserts: same count, same atoms, same order. An empty certificate falls
    // through here and is rejected because no disjunction has zero arms.
    //
    // A case that declines to name a disjunct is NOT rejected: its atoms are then
    // all bound as conjuncts, so it refutes the query on its own and the
    // disjunction is irrelevant. Rejecting it would be an unkillable guard.
    query_disjunctions(arena, assertions)
        .iter()
        .any(|disjuncts| {
            disjuncts.len() == certificate.cases.len()
                && certificate
                    .cases
                    .iter()
                    .zip(disjuncts)
                    .all(|(case, disjunct)| check_case(case, &asserted, Some(disjunct)))
        })
}

/// Stage 1 for one case: rebuild each carried atom and bind it to the query.
fn bind_case_atoms(
    case: &HandelmanCase,
    asserted: &[(NamedPoly, AtomSign)],
    disjunct: Option<&(NamedPoly, AtomSign)>,
) -> Option<Vec<(NamedPoly, AtomSign, Rational)>> {
    let mut bound = Vec::with_capacity(case.atoms.len());
    for (index, atom) in case.atoms.iter().enumerate() {
        let poly = from_wire(&atom.poly)?;
        let relaxation = wire_rational(atom.relaxation)?;
        let is_case_atom = case.case_atom == Some(index);
        let recognised = if is_case_atom {
            // The designated atom must be THIS case's disjunct — not merely
            // something the query asserts somewhere.
            disjunct.is_some_and(|(d_poly, d_sign)| *d_poly == poly && *d_sign == atom.sign)
        } else {
            asserted
                .iter()
                .any(|(found, found_sign)| *found == poly && *found_sign == atom.sign)
        };
        if !recognised {
            return None;
        }
        bound.push((poly, atom.sign, relaxation));
    }
    Some(bound)
}

/// Re-validate one case: bind its atoms, re-derive the combination, apply the
/// sign rule.
fn check_case(
    case: &HandelmanCase,
    asserted: &[(NamedPoly, AtomSign)],
    disjunct: Option<&(NamedPoly, AtomSign)>,
) -> bool {
    let Some(bound) = bind_case_atoms(case, asserted, disjunct) else {
        return false;
    };
    let Some(residual) = wire_rational(case.residual) else {
        return false;
    };

    let mut sum = NamedPoly::default();
    let mut has_strict_product = false;
    for product in &case.products {
        let Some(coefficient) = wire_rational(product.coefficient) else {
            return false;
        };
        // A zero or negative coefficient is not a Handelman multiplier: it would
        // let the combination subtract a nonnegative quantity.
        if coefficient.checked_cmp(&Rational::zero()) != Some(core::cmp::Ordering::Greater) {
            return false;
        }
        let mut term = NamedPoly::constant(coefficient);
        let mut strict = true;
        for &factor in &product.factors {
            let Some((poly, sign, relaxation)) = bound.get(factor) else {
                return false;
            };
            let Some((nonnegative, factor_strict)) = nonnegative_form(poly, *sign, *relaxation)
            else {
                return false;
            };
            let Some(next) = term.mul(&nonnegative) else {
                return false;
            };
            term = next;
            strict &= factor_strict;
        }
        if strict {
            has_strict_product = true;
        }
        let Some(next) = sum.add(&term) else {
            return false;
        };
        sum = next;
    }

    for (multiplier, index) in &case.equalities {
        let Some((poly, sign, _)) = bound.get(*index) else {
            return false;
        };
        // Only a genuine equality contributes zero regardless of its multiplier.
        // Give a `>= 0` atom a free-sign multiplier and the combination can
        // SUBTRACT a hypothesis, which refutes satisfiable queries.
        if *sign != AtomSign::Zero {
            return false;
        }
        let Some(multiplier) = from_wire(multiplier) else {
            return false;
        };
        let Some(term) = multiplier.mul(poly) else {
            return false;
        };
        let Some(next) = sum.add(&term) else {
            return false;
        };
        sum = next;
    }

    // Stage 2: the combination really is the residual constant.
    if sum != NamedPoly::constant(residual) {
        return false;
    }
    // Stage 3: and the residual really contradicts.
    residual_refutes(residual, has_strict_product) == Some(true)
}

/// A candidate polynomial the LP may combine, and what it came from.
#[derive(Clone, Debug)]
struct Generator {
    poly: NamedPoly,
    kind: GeneratorKind,
    /// `true` when the generator is `> 0` rather than `≥ 0`. Meaningless for an
    /// equality generator.
    strict: bool,
}

#[derive(Clone, Debug)]
enum GeneratorKind {
    /// A product of the case's atoms (empty = the constant `1`), nonnegative.
    Product(Vec<usize>),
    /// A monomial multiple of an equality atom; contributes zero.
    Equality { atom: usize, mono: Mono },
}

/// Round `value` UP to the nearest multiple of `10^-grid`, without ever forming
/// `numerator · 10^grid` (which overflows for exactly the constants that make
/// this necessary).
fn round_up_to_grid(value: Rational, grid: u32) -> Option<Rational> {
    let scale = 10_i128.checked_pow(grid)?;
    let (num, den) = (value.numerator(), value.denominator());
    let whole = num.div_euclid(den);
    let remainder = num.rem_euclid(den); // 0 <= remainder < den
    let scaled = remainder.checked_mul(scale)?;
    let ceiling = scaled.div_euclid(den) + i128::from(scaled.rem_euclid(den) != 0);
    let fraction = Rational::checked_new(ceiling, scale)?;
    Rational::checked_new(whole, 1)?.checked_add(fraction)
}

/// The relaxation to give each atom at this grid: zero unless the atom's
/// nonnegative form has a constant term whose denominator is beyond what exact
/// `i128` products can carry.
///
/// `None` for "no atom needs relaxing at all", so the caller can skip the grid
/// sweep entirely rather than repeat the unrelaxed attempt five times.
fn relaxations_at_grid(atoms: &[(NamedPoly, AtomSign)], grid: u32) -> Option<Vec<Rational>> {
    let mut out = Vec::with_capacity(atoms.len());
    let mut any = false;
    for (poly, sign) in atoms {
        let zero = Rational::zero();
        let Some((nonnegative, _)) = nonnegative_form(poly, *sign, zero) else {
            out.push(zero);
            continue;
        };
        let constant = nonnegative.constant_term();
        if constant.denominator() <= RELAXATION_DENOMINATOR_THRESHOLD {
            out.push(zero);
            continue;
        }
        let rounded = round_up_to_grid(constant, grid)?;
        let slack = rounded.checked_sub(constant)?;
        if slack.checked_cmp(&zero) == Some(core::cmp::Ordering::Less) {
            return None;
        }
        any = true;
        out.push(slack);
    }
    if any { Some(out) } else { None }
}

/// Build the generator set for one case at one degree cap.
fn generators(
    atoms: &[(NamedPoly, AtomSign)],
    relaxations: &[Rational],
    degree_cap: u32,
) -> Option<Vec<Generator>> {
    let effective: Vec<Option<(NamedPoly, bool)>> = atoms
        .iter()
        .zip(relaxations)
        .map(|((poly, sign), &relaxation)| nonnegative_form(poly, *sign, relaxation))
        .collect();

    let mut out = vec![Generator {
        poly: NamedPoly::constant(Rational::integer(1)),
        kind: GeneratorKind::Product(Vec::new()),
        strict: true,
    }];
    for (index, slot) in effective.iter().enumerate() {
        if let Some((poly, strict)) = slot
            && poly.degree() <= degree_cap
            && !poly.is_zero()
        {
            out.push(Generator {
                poly: poly.clone(),
                kind: GeneratorKind::Product(vec![index]),
                strict: *strict,
            });
        }
    }
    for (i, left) in effective.iter().enumerate() {
        for (j, right) in effective.iter().enumerate().skip(i) {
            let (Some((left_poly, left_strict)), Some((right_poly, right_strict))) = (left, right)
            else {
                continue;
            };
            if left_poly.degree() + right_poly.degree() > degree_cap {
                continue;
            }
            // Overflow here is a generator we simply do not offer the LP.
            let Some(product) = left_poly.mul(right_poly) else {
                continue;
            };
            if product.is_zero() {
                continue;
            }
            out.push(Generator {
                poly: product,
                kind: GeneratorKind::Product(vec![i, j]),
                strict: *left_strict && *right_strict,
            });
        }
    }
    // Equality atoms, times the constant monomial and each variable: enough for
    // a degree-1 polynomial multiplier, which is what the corpus shape needs.
    let mut variables: Vec<String> = atoms
        .iter()
        .flat_map(|(poly, _)| poly.variables())
        .collect();
    variables.sort();
    variables.dedup();
    for (index, (poly, sign)) in atoms.iter().enumerate() {
        if *sign != AtomSign::Zero || poly.is_zero() {
            continue;
        }
        let mut monomials: Vec<Mono> = vec![Vec::new()];
        monomials.extend(variables.iter().map(|name| vec![(name.clone(), 1_u32)]));
        for mono in monomials {
            let multiplier = match mono.first() {
                None => NamedPoly::constant(Rational::integer(1)),
                Some((name, _)) => NamedPoly::var(name),
            };
            let Some(product) = multiplier.mul(poly) else {
                continue;
            };
            if product.degree() > degree_cap || product.is_zero() {
                continue;
            }
            out.push(Generator {
                poly: product,
                kind: GeneratorKind::Equality { atom: index, mono },
                strict: false,
            });
        }
    }
    if out.len() > MAX_GENERATORS {
        return None;
    }
    Some(out)
}

/// The distinct non-constant monomials across `generators`, in a deterministic
/// order.
fn monomial_basis(generators: &[Generator]) -> Option<Vec<Mono>> {
    let mut basis: Vec<Mono> = generators
        .iter()
        .flat_map(|g| g.poly.terms().map(|(mono, _)| mono.clone()))
        .filter(|mono| !mono.is_empty())
        .collect();
    basis.sort();
    basis.dedup();
    if basis.len() > MAX_MONOMIALS {
        return None;
    }
    Some(basis)
}

/// Hand the monomial-abstracted linear system to the exact Farkas engine and
/// read back one multiplier per generator.
///
/// Returns `None` whenever the abstraction is satisfiable, the engine declines,
/// or anything about the read-back does not reconstruct exactly.
fn farkas_multipliers(generators: &[Generator], basis: &[Mono]) -> Option<Vec<Rational>> {
    let mut abstraction = TermArena::new();
    let mut variables = Vec::with_capacity(basis.len());
    for index in 0..basis.len() {
        variables.push(abstraction.real_var(&format!("m{index}")).ok()?);
    }
    let zero = abstraction.real_const(Rational::zero());

    let mut asserted = Vec::with_capacity(generators.len());
    for generator in generators {
        let mut expression = abstraction.real_const(generator.poly.constant_term());
        for (mono, &coeff) in generator.poly.terms() {
            if mono.is_empty() {
                continue;
            }
            let position = basis.iter().position(|candidate| candidate == mono)?;
            let scaled = {
                let constant = abstraction.real_const(coeff);
                abstraction.real_mul(constant, variables[position]).ok()?
            };
            expression = abstraction.real_add(expression, scaled).ok()?;
        }
        let relation = match generator.kind {
            GeneratorKind::Equality { .. } => abstraction.eq(expression, zero).ok()?,
            GeneratorKind::Product(_) if generator.strict => {
                abstraction.real_gt(expression, zero).ok()?
            }
            GeneratorKind::Product(_) => abstraction.real_ge(expression, zero).ok()?,
        };
        asserted.push(relation);
    }

    let certificate = crate::lra::lra_farkas_certificate(&abstraction, &asserted).ok()??;
    if !certificate.verify() {
        return None;
    }

    // The Farkas atoms are in the engine's own normal form: each is some
    // rational multiple of the generator it came from. Recover that multiple
    // rather than assuming a normalization, then accumulate
    // `μ_g = −Σ λ_i · scale_i` — the sign flip is because the engine's atoms are
    // `expr ≤ 0` bounds while a generator is `poly ≥ 0`.
    let mut multipliers = vec![Rational::zero(); generators.len()];
    for (index, atom) in certificate.atoms.iter().enumerate() {
        let lambda = *certificate.multipliers.get(index)?;
        if lambda.is_zero() {
            continue;
        }
        let generator_index = *certificate.origins.get(index)?;
        let generator = generators.get(generator_index)?;
        let mut rebuilt = NamedPoly::constant(atom.constant);
        for &(dense, coeff) in &atom.coeffs {
            let symbol = *certificate.vars.get(dense)?;
            let name = abstraction.symbol(symbol).0;
            let position: usize = name.strip_prefix('m')?.parse().ok()?;
            rebuilt.add_term(basis.get(position)?.clone(), coeff)?;
        }
        let scale = proportionality(&rebuilt, &generator.poly)?;
        let contribution = lambda.checked_mul(scale)?.checked_neg()?;
        multipliers[generator_index] = multipliers[generator_index].checked_add(contribution)?;
    }
    Some(multipliers)
}

/// The unique `s` with `lhs == s · rhs`, or `None` when no such `s` exists.
fn proportionality(lhs: &NamedPoly, rhs: &NamedPoly) -> Option<Rational> {
    let (mono, rhs_coeff) = rhs.terms().next()?;
    let lhs_coeff = lhs.terms().find(|(m, _)| *m == mono).map(|(_, c)| *c)?;
    let scale = lhs_coeff.checked_div(*rhs_coeff)?;
    if rhs.scale(scale)? == *lhs {
        Some(scale)
    } else {
        None
    }
}

/// Assemble a case from the LP's multipliers, or decline.
fn assemble_case(
    atoms: &[(NamedPoly, AtomSign)],
    relaxations: &[Rational],
    case_atom: Option<usize>,
    generators: &[Generator],
    multipliers: &[Rational],
) -> Option<HandelmanCase> {
    let mut products = Vec::new();
    let mut equality_terms: BTreeMap<usize, NamedPoly> = BTreeMap::new();
    let mut sum = NamedPoly::default();
    for (generator, &multiplier) in generators.iter().zip(multipliers) {
        if multiplier.is_zero() {
            continue;
        }
        match &generator.kind {
            GeneratorKind::Product(factors) => {
                if multiplier.checked_cmp(&Rational::zero())? != core::cmp::Ordering::Greater {
                    return None;
                }
                products.push(HandelmanProduct {
                    coefficient: (multiplier.numerator(), multiplier.denominator()),
                    factors: factors.clone(),
                });
            }
            GeneratorKind::Equality { atom, mono } => {
                let slot = equality_terms.entry(*atom).or_default();
                slot.add_term(mono.clone(), multiplier)?;
            }
        }
        sum = sum.add(&generator.poly.scale(multiplier)?)?;
    }
    // The combination must have collapsed to a constant.
    if sum.terms().any(|(mono, _)| !mono.is_empty()) {
        return None;
    }
    let residual = sum.constant_term();
    let equalities: Vec<(WirePoly, usize)> = equality_terms
        .into_iter()
        .filter(|(_, poly)| !poly.is_zero())
        .map(|(atom, poly)| (poly.to_wire(), atom))
        .collect();
    Some(HandelmanCase {
        atoms: atoms
            .iter()
            .zip(relaxations)
            .map(|((poly, sign), relaxation)| HandelmanAtom {
                poly: poly.to_wire(),
                sign: *sign,
                relaxation: (relaxation.numerator(), relaxation.denominator()),
            })
            .collect(),
        case_atom,
        products,
        equalities,
        residual: (residual.numerator(), residual.denominator()),
    })
}

/// Search for a combination refuting one case.
fn refute_case(atoms: &[(NamedPoly, AtomSign)], case_atom: Option<usize>) -> Option<HandelmanCase> {
    let max_degree = atoms.iter().map(|(poly, _)| poly.degree()).max()?.max(1);
    // Unrelaxed first, then progressively coarser roundings of any constant term
    // no exact `i128` product can carry.
    let mut schedules: Vec<Vec<Rational>> = vec![vec![Rational::zero(); atoms.len()]];
    for grid in RELAXATION_GRIDS {
        if let Some(relaxations) = relaxations_at_grid(atoms, grid) {
            schedules.push(relaxations);
        }
    }
    for relaxations in &schedules {
        // Lowest degree cap first: it keeps the abstraction small, and the
        // refutation it finds is the one a reader can follow.
        for degree_cap in max_degree..=max_degree.saturating_add(2) {
            let Some(generators) = generators(atoms, relaxations, degree_cap) else {
                continue;
            };
            let Some(basis) = monomial_basis(&generators) else {
                continue;
            };
            let Some(multipliers) = farkas_multipliers(&generators, &basis) else {
                continue;
            };
            if let Some(case) =
                assemble_case(atoms, relaxations, case_atom, &generators, &multipliers)
            {
                return Some(case);
            }
        }
    }
    None
}

/// Derive a Handelman refutation from the exact source query, or decline.
///
/// The result is re-validated with [`check_handelman_refutation`] before it is
/// returned, so a returned certificate always checks.
///
/// # That last re-validation kills no test, and that is measured, not assumed
///
/// Mutating it away (`.find(check)` -> `.next()`) leaves all 23 tests in this
/// module green. Every rejection it could make is already made upstream:
/// `assemble_case` refuses a non-positive multiplier and a combination that does
/// not collapse to a constant, the atoms are asserted by construction, and the
/// engine's own `FarkasCertificate::verify` guarantees the combined relation is
/// unsatisfiable — which is exactly `residual_refutes`'s precondition. So no
/// fixture can pass everything else and fail only here.
///
/// It is kept anyway, on the same terms as `lra_farkas_certificate`'s self-check
/// and `nra_product_cert`'s zero-exponent screen: it makes "a returned
/// certificate always checks" a property of the code rather than of this
/// paragraph, and it is the thing that would fire first if the read-back from
/// the LP ever stopped agreeing with the checker.
#[must_use]
pub fn handelman_refutation(
    arena: &TermArena,
    assertions: &[TermId],
) -> Option<HandelmanRefutationCertificate> {
    let atoms = query_atoms(arena, assertions);
    if atoms.is_empty() {
        return None;
    }
    // NONLINEAR only. Every purely linear refutation is a Farkas refutation, and
    // the linear route already produces one (with an Alethe proof besides). A
    // Handelman certificate for `x > 5, x < 3` is correct and strictly worse
    // evidence, so this route declines rather than hijacking `QF_LRA`.
    let disjunctions = query_disjunctions(arena, assertions);
    let highest_degree = atoms
        .iter()
        .chain(disjunctions.iter().flatten())
        .map(|(poly, _)| poly.degree())
        .max()
        .unwrap_or(0);
    if highest_degree < 2 {
        return None;
    }
    let mut candidates: Vec<HandelmanRefutationCertificate> = Vec::new();
    if let Some(case) = refute_case(&atoms, None) {
        candidates.push(HandelmanRefutationCertificate { cases: vec![case] });
    }
    if candidates.is_empty() {
        for disjuncts in disjunctions {
            let cases: Option<Vec<HandelmanCase>> = disjuncts
                .iter()
                .map(|disjunct| {
                    let mut case_atoms = atoms.clone();
                    case_atoms.push(disjunct.clone());
                    refute_case(&case_atoms, Some(case_atoms.len() - 1))
                })
                .collect();
            if let Some(cases) = cases {
                candidates.push(HandelmanRefutationCertificate { cases });
                break;
            }
        }
    }
    candidates
        .into_iter()
        .find(|certificate| check_handelman_refutation(arena, assertions, certificate))
}

#[cfg(test)]
mod tests {
    use super::*;
    use axeyum_smtlib::parse_script;

    /// `cli__regress1__nl__coeff-unsat.smt2`, verbatim.
    const COEFF_UNSAT: &str = "(set-logic QF_NRA)\n\
        (declare-fun a () Real)\n(declare-fun b () Real)\n\
        (assert (> a 0))\n(assert (> b 0))\n\
        (assert (>= a (* 3 b)))\n\
        (assert (< (* a a) (* 8 b b)))\n(check-sat)";

    /// `cli__regress1__nl__combine.smt2`, verbatim.
    const COMBINE: &str = "(set-logic QF_NRA)\n\
        (declare-fun a () Real)\n(declare-fun b () Real)\n(declare-fun c () Real)\n\
        (assert (> c 1))\n(assert (> (* a b) 1))\n\
        (assert (< (* a b c) 1))\n(check-sat)";

    /// `cli__regress1__nl__approx-sqrt-unsat.smt2`, verbatim. The third disjunct
    /// is the one whose exact refutation does not fit in `i128`.
    const APPROX_SQRT: &str = "(set-logic QF_NRA)\n\
        (declare-fun x () Real)\n\
        (assert (= (* x x) 2))\n\
        (assert (> x 0))\n\
        (assert (or \n\
        (> (+ (* x x) (* (- 2.8) x)) (- 1.95))\n\
        (> (+ (* x x) (* (- 2.8284271247) x)) (- 1.999999))\n\
        (> (+ (* x x) (* (- 2.82842712475) x)) \
           (- 2.0000000000000000000000000001))\n\
        ))\n(check-sat)";

    /// **SATISFIABLE** at `x = y = 0`. `x ≥ 0` and `y ≥ 0` give `xy ≥ 0`, and the
    /// combination `1·(x·y) + 1·(−xy) ≡ 0` is a perfectly valid identity — it just
    /// refutes nothing, because a sum of NON-strict nonnegatives can be zero.
    const NONSTRICT_SAT: &str = "(set-logic QF_NRA)\n\
        (declare-fun x () Real)(declare-fun y () Real)\n\
        (assert (>= x 0))(assert (>= y 0))(assert (<= (* x y) 0))\n(check-sat)";

    /// **SATISFIABLE** at `x = 0.5`.
    const OPEN_UNIT_INTERVAL: &str = "(set-logic QF_NRA)\n\
        (declare-fun x () Real)\n\
        (assert (> x 0))(assert (< x 1))(assert (> (* x x) 0))\n(check-sat)";

    fn query(text: &str) -> (axeyum_ir::TermArena, Vec<TermId>) {
        let parsed = parse_script(text).expect("parses");
        (parsed.arena, parsed.assertions)
    }

    fn v(name: &str) -> NamedPoly {
        NamedPoly::var(name)
    }

    fn k(value: i128) -> NamedPoly {
        NamedPoly::constant(Rational::integer(value))
    }

    fn hypothesis(poly: &NamedPoly, sign: AtomSign, relaxation: WireRat) -> HandelmanAtom {
        HandelmanAtom {
            poly: poly.to_wire(),
            sign,
            relaxation,
        }
    }

    fn product(coefficient: WireRat, factors: &[usize]) -> HandelmanProduct {
        HandelmanProduct {
            coefficient,
            factors: factors.to_vec(),
        }
    }

    fn case(
        atoms: Vec<HandelmanAtom>,
        case_atom: Option<usize>,
        products: Vec<HandelmanProduct>,
        equalities: Vec<(WirePoly, usize)>,
        residual: WireRat,
    ) -> HandelmanCase {
        HandelmanCase {
            atoms,
            case_atom,
            products,
            equalities,
            residual,
        }
    }

    fn certificate_for(text: &str) -> HandelmanRefutationCertificate {
        let (arena, assertions) = query(text);
        handelman_refutation(&arena, &assertions).expect("certificate")
    }

    // ---------------------------------------------------------------- corpus

    #[test]
    fn all_three_corpus_shapes_certify_and_survive_a_fresh_parse() {
        for text in [COEFF_UNSAT, COMBINE, APPROX_SQRT] {
            let (arena, assertions) = query(text);
            let certificate =
                handelman_refutation(&arena, &assertions).expect("a certificate exists");
            assert!(check_handelman_refutation(
                &arena,
                &assertions,
                &certificate
            ));
            // ...and against a parse sharing no state with the producing run,
            // which is what the name-keyed polynomial exists for.
            let (fresh, fresh_assertions) = query(text);
            assert!(check_handelman_refutation(
                &fresh,
                &fresh_assertions,
                &certificate
            ));
        }
    }

    #[test]
    fn the_conjunctive_shapes_need_more_than_one_product() {
        // The whole reason this module exists: `nra_product_cert` declines these
        // two because ONE product does not close them.
        for text in [COEFF_UNSAT, COMBINE] {
            let certificate = certificate_for(text);
            assert_eq!(certificate.cases().len(), 1);
            assert!(
                certificate.cases()[0].products().len() >= 3,
                "{text}: a single-product refutation would belong in nra_product_cert"
            );
        }
        let (arena, assertions) = query(COEFF_UNSAT);
        assert!(
            crate::nra_product_cert::real_product_refutation(&arena, &assertions).is_none(),
            "if the two-factor route learned this shape, this module's premise changed"
        );
    }

    #[test]
    fn the_case_split_covers_every_disjunct_of_the_three_way_or() {
        let certificate = certificate_for(APPROX_SQRT);
        assert!(certificate.is_case_split());
        assert_eq!(certificate.cases().len(), 3);
        for one in certificate.cases() {
            assert!(one.case_atom().is_some());
            // Each disjunct is refuted against the equality `x² − 2 = 0`, which
            // needs a genuine polynomial multiplier, not just a constant one.
            assert!(!one.products().is_empty());
        }
    }

    #[test]
    fn only_the_disjunct_that_needs_it_carries_a_relaxation() {
        // Disjuncts 1 and 2 have small constants and are refuted exactly.
        // Disjunct 3's constant is `2.0000000000000000000000000001`, and the
        // tight refutation needs `(2+k)²`, whose numerator is 1.6·10^57.
        let certificate = certificate_for(APPROX_SQRT);
        let relaxed: Vec<usize> = certificate
            .cases()
            .iter()
            .enumerate()
            .filter(|(_, one)| one.atoms().iter().any(|a| a.relaxation().0 != 0))
            .map(|(index, _)| index)
            .collect();
        assert_eq!(
            relaxed,
            vec![2],
            "only the 10^28-denominator disjunct should need weakening"
        );
    }

    #[test]
    fn the_first_disjunct_is_refuted_by_the_number_a_reader_can_check() {
        // `x² = 2` and `x² − 2.8x + 1.95 > 0` give `x < 3.95/2.8`, so
        // `x² < (3.95/2.8)² = 1.99011…`, missing 2 by 0.0775/7.84. The residual
        // is that miss, and it is in the certificate rather than in a comment.
        let certificate = certificate_for(APPROX_SQRT);
        assert_eq!(certificate.cases()[0].residual(), (-31, 400));
    }

    // ------------------------------------------------- producer declines

    #[test]
    fn a_purely_linear_refutation_is_declined() {
        // Correct but strictly worse evidence than the Farkas refutation the
        // linear route already produces, so this route must not take it.
        let (arena, assertions) = query(
            "(set-logic QF_LRA)\n(declare-fun x () Real)\n\
             (assert (> x 5))(assert (< x 3))\n(check-sat)",
        );
        assert!(handelman_refutation(&arena, &assertions).is_none());
    }

    #[test]
    fn the_producer_declines_satisfiable_nonlinear_queries() {
        for text in [NONSTRICT_SAT, OPEN_UNIT_INTERVAL] {
            let (arena, assertions) = query(text);
            assert!(
                handelman_refutation(&arena, &assertions).is_none(),
                "{text} is satisfiable"
            );
        }
    }

    #[test]
    fn strict_factors_do_refute_what_nonstrict_ones_cannot() {
        // The positive half of the strictness rule. Without it, "never certify a
        // zero residual" would pass every soundness test in this file while
        // making the module useless.
        let (arena, assertions) = query(
            "(set-logic QF_NRA)\n(declare-fun x () Real)(declare-fun y () Real)\n\
             (assert (> x 0))(assert (> y 0))(assert (<= (* x y) 0))\n(check-sat)",
        );
        let certificate = handelman_refutation(&arena, &assertions).expect("certificate");
        assert!(check_handelman_refutation(
            &arena,
            &assertions,
            &certificate
        ));
        assert_eq!(certificate.cases()[0].residual().0, 0);
    }

    // ------------------------------------------------------ checker guards

    #[test]
    fn a_certificate_for_another_query_is_rejected() {
        let certificate = certificate_for(COEFF_UNSAT);
        let (arena, assertions) = query(COMBINE);
        assert!(!check_handelman_refutation(
            &arena,
            &assertions,
            &certificate
        ));
    }

    #[test]
    fn a_hypothesis_the_query_does_not_assert_is_rejected() {
        // Stage 1 in isolation: `a > 0` is asserted, `a >= 0` is not, and the
        // swap silently turns a strict product into a non-strict one.
        let mut certificate = certificate_for(COEFF_UNSAT);
        certificate.cases[0].atoms[0].sign = AtomSign::Nonnegative;
        let (arena, assertions) = query(COEFF_UNSAT);
        assert!(!check_handelman_refutation(
            &arena,
            &assertions,
            &certificate
        ));
    }

    #[test]
    fn a_nonstrict_combination_summing_to_zero_refutes_nothing() {
        // **THE soundness case.** Every part of this forgery is real: `x ≥ 0`,
        // `y ≥ 0` and `xy ≤ 0` are all asserted, and `1·(x·y) + 1·(−xy)` really
        // is identically 0. It is still not a refutation — the query is
        // satisfiable at `x = y = 0` — because a sum of NON-strict nonnegative
        // terms is allowed to be zero. Only the strictness rule stops it.
        let (arena, assertions) = query(NONSTRICT_SAT);
        let xy = v("x").mul(&v("y")).expect("xy");
        let forged = HandelmanRefutationCertificate {
            cases: vec![case(
                vec![
                    hypothesis(&v("x"), AtomSign::Nonnegative, (0, 1)),
                    hypothesis(&v("y"), AtomSign::Nonnegative, (0, 1)),
                    hypothesis(&xy, AtomSign::Nonpositive, (0, 1)),
                ],
                None,
                vec![product((1, 1), &[0, 1]), product((1, 1), &[2])],
                Vec::new(),
                (0, 1),
            )],
        };
        assert!(
            !check_handelman_refutation(&arena, &assertions, &forged),
            "a zero residual closes only when some product is strictly positive"
        );
    }

    #[test]
    fn a_positive_residual_refutes_nothing() {
        // `1 > 0` is true and `Σ = 1` is a correct identity. It contradicts
        // nothing, and a checker that read "the sum is a constant" as "the sum is
        // impossible" would certify every query in the corpus.
        let (arena, assertions) = query(OPEN_UNIT_INTERVAL);
        let forged = HandelmanRefutationCertificate {
            cases: vec![case(
                vec![hypothesis(&v("x"), AtomSign::Positive, (0, 1))],
                None,
                vec![product((1, 1), &[])],
                Vec::new(),
                (1, 1),
            )],
        };
        assert!(!check_handelman_refutation(&arena, &assertions, &forged));
    }

    #[test]
    fn a_nonpositive_coefficient_is_rejected() {
        // `−1·x + −1·(1−x) ≡ −1` is an exact identity over two genuinely asserted
        // hypotheses, and −1 < 0 would close. But a NEGATIVE multiplier subtracts
        // a nonnegative quantity, which is not a Handelman combination at all:
        // the query is satisfiable at x = 0.5.
        let (arena, assertions) = query(OPEN_UNIT_INTERVAL);
        let x_minus_one = v("x").sub(&k(1)).expect("x − 1");
        let forged = HandelmanRefutationCertificate {
            cases: vec![case(
                vec![
                    hypothesis(&v("x"), AtomSign::Positive, (0, 1)),
                    hypothesis(&x_minus_one, AtomSign::Negative, (0, 1)),
                ],
                None,
                vec![product((-1, 1), &[0]), product((-1, 1), &[1])],
                Vec::new(),
                (-1, 1),
            )],
        };
        assert!(!check_handelman_refutation(&arena, &assertions, &forged));
    }

    #[test]
    fn a_negative_relaxation_is_rejected() {
        // A relaxation WEAKENS a hypothesis, which is why it is allowed at all.
        // A negative one strengthens it into something the query never said:
        // here `x > 0` is bent into `x − 1 > 0`, and `(x−1) + (1−x) ≡ 0` then
        // "refutes" the satisfiable `0 < x < 1`.
        let (arena, assertions) = query(OPEN_UNIT_INTERVAL);
        let x_minus_one = v("x").sub(&k(1)).expect("x − 1");
        let forged = HandelmanRefutationCertificate {
            cases: vec![case(
                vec![
                    hypothesis(&v("x"), AtomSign::Positive, (-1, 1)),
                    hypothesis(&x_minus_one, AtomSign::Negative, (0, 1)),
                ],
                None,
                vec![product((1, 1), &[0]), product((1, 1), &[1])],
                Vec::new(),
                (0, 1),
            )],
        };
        assert!(!check_handelman_refutation(&arena, &assertions, &forged));
    }

    #[test]
    fn an_equality_is_never_a_strictly_positive_factor() {
        // `x = 1` says `x − 1 ≥ 0` and `x − 1 ≤ 0`; it never says `x − 1 > 0`.
        // Reading an equality as a strict lower bound makes
        // `1·(x−1) + (−1)·(x−1) ≡ 0` close on strictness and refutes a query with
        // a model.
        let (arena, assertions) = query(
            "(set-logic QF_NRA)\n(declare-fun x () Real)\n\
             (assert (= x 1))(assert (>= (* x x) 1))\n(check-sat)",
        );
        let x_minus_one = v("x").sub(&k(1)).expect("x − 1");
        let minus_one = k(-1);
        let forged = HandelmanRefutationCertificate {
            cases: vec![case(
                vec![hypothesis(&x_minus_one, AtomSign::Zero, (0, 1))],
                None,
                vec![product((1, 1), &[0])],
                vec![(minus_one.to_wire(), 0)],
                (0, 1),
            )],
        };
        assert!(!check_handelman_refutation(&arena, &assertions, &forged));
    }

    #[test]
    fn a_free_sign_multiplier_is_refused_on_a_non_equality() {
        // An equality contributes zero whatever polynomial multiplies it, so its
        // multiplier's sign is unconstrained. Grant that to an INEQUALITY and the
        // combination can subtract a hypothesis: here `1·(x−1)` cancelled by
        // `(−1)·(x−1)` "refutes" the satisfiable `x > 1`.
        let (arena, assertions) = query(
            "(set-logic QF_NRA)\n(declare-fun x () Real)\n\
             (assert (> x 1))(assert (> (* x x) 1))\n(check-sat)",
        );
        let x_minus_one = v("x").sub(&k(1)).expect("x − 1");
        let minus_one = k(-1);
        let forged = HandelmanRefutationCertificate {
            cases: vec![case(
                vec![hypothesis(&x_minus_one, AtomSign::Positive, (0, 1))],
                None,
                vec![product((1, 1), &[0])],
                vec![(minus_one.to_wire(), 0)],
                (0, 1),
            )],
        };
        assert!(!check_handelman_refutation(&arena, &assertions, &forged));
    }

    #[test]
    fn a_combination_that_is_not_a_constant_is_rejected() {
        // Without this, `x > 0` alone "refutes" itself: the sum is `x`, the
        // carried residual is 0, and nothing checks that they agree.
        let (arena, assertions) = query(OPEN_UNIT_INTERVAL);
        let forged = HandelmanRefutationCertificate {
            cases: vec![case(
                vec![hypothesis(&v("x"), AtomSign::Positive, (0, 1))],
                None,
                vec![product((1, 1), &[0])],
                Vec::new(),
                (0, 1),
            )],
        };
        assert!(!check_handelman_refutation(&arena, &assertions, &forged));
    }

    #[test]
    fn a_partially_covered_case_split_is_rejected() {
        // The query is satisfiable at x = 200. One case refuting only the
        // `x < 0` arm proves nothing about the `x > 100` arm, and covering "some"
        // of a disjunction is the difference between a refutation and a guess.
        let (arena, assertions) = query(
            "(set-logic QF_NRA)\n(declare-fun x () Real)\n\
             (assert (> x 0))(assert (> (* x x) 0))\n\
             (assert (or (< x 0) (> x 100)))\n(check-sat)",
        );
        let forged = HandelmanRefutationCertificate {
            cases: vec![case(
                vec![
                    hypothesis(&v("x"), AtomSign::Positive, (0, 1)),
                    hypothesis(&v("x"), AtomSign::Negative, (0, 1)),
                ],
                Some(1),
                vec![product((1, 1), &[0]), product((1, 1), &[1])],
                Vec::new(),
                (0, 1),
            )],
        };
        assert!(!check_handelman_refutation(&arena, &assertions, &forged));
    }

    #[test]
    fn a_fabricated_case_atom_is_rejected() {
        // Two cases, so the coverage count matches the two-armed disjunction, but
        // the atom each case actually reasons from (`x < 0`) is neither asserted
        // nor a disjunct. The query is satisfiable at x = 7.
        let (arena, assertions) = query(
            "(set-logic QF_NRA)\n(declare-fun x () Real)\n\
             (assert (> x 0))(assert (> (* x x) 0))\n\
             (assert (or (> x 5) (> x 6)))\n(check-sat)",
        );
        let fabricated = case(
            vec![
                hypothesis(&v("x"), AtomSign::Positive, (0, 1)),
                hypothesis(&v("x"), AtomSign::Negative, (0, 1)),
            ],
            Some(1),
            vec![product((1, 1), &[0]), product((1, 1), &[1])],
            Vec::new(),
            (0, 1),
        );
        let forged = HandelmanRefutationCertificate {
            cases: vec![fabricated.clone(), fabricated],
        };
        assert!(!check_handelman_refutation(&arena, &assertions, &forged));
    }

    #[test]
    fn an_out_of_range_factor_index_is_rejected_rather_than_panicking() {
        let (arena, assertions) = query(OPEN_UNIT_INTERVAL);
        let forged = HandelmanRefutationCertificate {
            cases: vec![case(
                vec![hypothesis(&v("x"), AtomSign::Positive, (0, 1))],
                None,
                vec![product((1, 1), &[7])],
                Vec::new(),
                (-1, 1),
            )],
        };
        assert!(!check_handelman_refutation(&arena, &assertions, &forged));
    }

    #[test]
    fn a_zero_denominator_is_rejected_rather_than_panicking() {
        // `Rational::checked_new` ASSERTS on a zero denominator, so a forged wire
        // value reaches a panic unless it is screened first.
        let (arena, assertions) = query(OPEN_UNIT_INTERVAL);
        let mut forged = HandelmanRefutationCertificate {
            cases: vec![case(
                vec![hypothesis(&v("x"), AtomSign::Positive, (0, 0))],
                None,
                vec![product((1, 1), &[0])],
                Vec::new(),
                (-1, 1),
            )],
        };
        assert!(!check_handelman_refutation(&arena, &assertions, &forged));
        forged.cases[0].atoms[0].relaxation = (0, 1);
        forged.cases[0].residual = (-1, 0);
        assert!(!check_handelman_refutation(&arena, &assertions, &forged));
        forged.cases[0].residual = (-1, 1);
        forged.cases[0].products[0].coefficient = (1, 0);
        assert!(!check_handelman_refutation(&arena, &assertions, &forged));
    }

    // --------------------------------------------------------- arithmetic

    #[test]
    fn rounding_to_a_grid_never_rounds_down_and_survives_a_10_pow_28_denominator() {
        // The constant that forced relaxations to exist at all.
        let awkward = Rational::checked_new(
            20_000_000_000_000_000_000_000_000_001,
            10_000_000_000_000_000_000_000_000_000,
        )
        .expect("2 + 10^-28");
        let rounded = round_up_to_grid(awkward, 12).expect("rounds");
        assert_eq!(
            rounded,
            Rational::checked_new(2_000_000_000_001, 1_000_000_000_000).unwrap()
        );
        assert_eq!(
            rounded.checked_cmp(&awkward),
            Some(core::cmp::Ordering::Greater)
        );
        // Already on the grid: unchanged, not bumped.
        let exact = Rational::integer(2);
        assert_eq!(round_up_to_grid(exact, 12), Some(exact));
        // Negative values round toward zero's side but never downward.
        let negative = Rational::checked_new(-3, 2).expect("−1.5");
        let rounded = round_up_to_grid(negative, 1).expect("rounds");
        assert_ne!(
            rounded.checked_cmp(&negative),
            Some(core::cmp::Ordering::Less)
        );
    }

    #[test]
    fn the_residual_rule_is_the_only_place_strictness_is_decided() {
        assert_eq!(
            residual_refutes(Rational::integer(-1), false),
            Some(true),
            "a negative residual closes with or without strictness"
        );
        assert_eq!(residual_refutes(Rational::zero(), true), Some(true));
        assert_eq!(
            residual_refutes(Rational::zero(), false),
            Some(false),
            "a sum of non-strict nonnegatives is allowed to be zero"
        );
        assert_eq!(residual_refutes(Rational::integer(1), true), Some(false));
    }
}
