//! Bounded bit-packed polynomials and irreducibility certificates over `GF(2)`.
//!
//! Search is not trusted.  [`certify_irreducible`] emits the polynomial
//! identities required by Rabin's criterion, and [`check_irreducible_certificate`]
//! checks those identities without calling the producer's irreducibility
//! verdict.  All potentially large work runs through [`Gf2Context`].

use core::fmt;

use num_bigint::BigUint;

/// A normalized polynomial over `GF(2)`, packed coefficient-first into words.
///
/// Bit `i` is the coefficient of `x^i`; trailing zero words are absent.
#[derive(Clone, Default, Eq, PartialEq)]
pub struct Gf2Poly {
    words: Vec<u64>,
}

impl fmt::Debug for Gf2Poly {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("Gf2Poly")
            .field("exponents", &self.exponents())
            .finish()
    }
}

impl Gf2Poly {
    /// Construct from little-endian coefficient words and normalize.
    #[must_use]
    pub fn from_words(mut words: Vec<u64>) -> Self {
        trim(&mut words);
        Self { words }
    }

    /// Construct from a list of nonzero exponents under an allocation limit.
    ///
    /// # Errors
    ///
    /// Returns [`Gf2Error::DegreeLimit`] when the largest exponent exceeds the
    /// intermediate-polynomial ceiling.
    pub fn from_exponents(exponents: &[usize], limits: Gf2Limits) -> Result<Self, Gf2Error> {
        let degree = exponents.iter().copied().max().unwrap_or(0);
        if !exponents.is_empty() && degree > limits.max_intermediate_degree {
            return Err(Gf2Error::DegreeLimit {
                observed: degree,
                limit: limits.max_intermediate_degree,
            });
        }
        let word_count = if exponents.is_empty() {
            0
        } else {
            degree / 64 + 1
        };
        let mut words = vec![0; word_count];
        for &exponent in exponents {
            words[exponent / 64] ^= 1_u64 << (exponent % 64);
        }
        Ok(Self::from_words(words))
    }

    /// The zero polynomial.
    #[must_use]
    pub const fn zero() -> Self {
        Self { words: Vec::new() }
    }

    /// The constant polynomial one.
    #[must_use]
    pub fn one() -> Self {
        Self { words: vec![1] }
    }

    /// The polynomial `x`.
    #[must_use]
    pub fn x() -> Self {
        Self { words: vec![2] }
    }

    /// Return the coefficient words in canonical little-endian order.
    #[must_use]
    pub fn words(&self) -> &[u64] {
        &self.words
    }

    /// Return the degree, or `None` for zero.
    #[must_use]
    pub fn degree(&self) -> Option<usize> {
        let last = *self.words.last()?;
        let high = usize::try_from(u64::BITS - 1 - last.leading_zeros()).ok()?;
        Some((self.words.len() - 1) * 64 + high)
    }

    /// Whether this is zero.
    #[must_use]
    pub fn is_zero(&self) -> bool {
        self.words.is_empty()
    }

    /// Whether the coefficient at `exponent` is one.
    #[must_use]
    pub fn coefficient(&self, exponent: usize) -> bool {
        self.words
            .get(exponent / 64)
            .is_some_and(|word| word & (1_u64 << (exponent % 64)) != 0)
    }

    /// Return the nonzero exponents in ascending order.
    #[must_use]
    pub fn exponents(&self) -> Vec<usize> {
        let mut result = Vec::new();
        for (word_index, &source) in self.words.iter().enumerate() {
            let mut word = source;
            while word != 0 {
                let bit = usize::try_from(word.trailing_zeros()).unwrap_or(0);
                result.push(word_index * 64 + bit);
                word &= word - 1;
            }
        }
        result
    }

    /// Whether every nonleading term has degree at most half the degree.
    ///
    /// This is the non-strict polynomial shape in Lemire and Kaser's
    /// conjecture.  The zero polynomial has no leading term and returns
    /// `false`.
    #[must_use]
    pub fn is_half_degree_shaped(&self) -> bool {
        let Some(degree) = self.degree() else {
            return false;
        };
        self.exponents()
            .into_iter()
            .filter(|&exponent| exponent != degree)
            .all(|exponent| exponent <= degree / 2)
    }
}

/// Exact checked Rabin verdict retained by a parity-split report.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Gf2IrreducibilityVerdict {
    /// The Rabin producer emitted a certificate which its independent checker
    /// accepted.
    Irreducible,
    /// The exact Rabin criterion found a proper-factor obstruction and no
    /// irreducibility certificate can be emitted.
    Reducible,
}

/// Exact even/odd decomposition of a half-degree-shaped binary polynomial.
///
/// In characteristic two, writing the even and odd coefficient parts as
/// `E` and `H` gives `f(x)=E(x)^2+xH(x)^2`.  For odd
/// `degree(f)=2m+1`, `H` is monic of degree `m` and is itself half-degree
/// shaped.  For even `degree(f)=2m`, the same is true of `E`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct HalfDegreeParitySplitReport {
    /// Degree of the supplied half-degree-shaped polynomial.
    pub degree: usize,
    /// `floor(degree/2)`.
    pub half_degree: usize,
    /// Polynomial formed from the even coefficients of the input.
    pub even_component: Gf2Poly,
    /// Polynomial formed from the odd coefficients of the input.
    pub odd_component: Gf2Poly,
    /// Monic half-degree-shaped component carrying the leading term.
    pub recursive_component: Gf2Poly,
    /// The other parity component.
    pub complementary_component: Gf2Poly,
    /// Exact gcd of the two parity components.
    pub component_gcd: Gf2Poly,
    /// Exact gcd `gcd(f,f')`, independently reconstructed from the input.
    pub derivative_gcd: Gf2Poly,
    /// Independent Rabin verdict for the recursive component.
    pub recursive_component_irreducibility: Gf2IrreducibilityVerdict,
    /// Independent Rabin verdict for the supplied polynomial.
    pub polynomial_irreducibility: Gf2IrreducibilityVerdict,
}

impl HalfDegreeParitySplitReport {
    /// Whether `gcd(E,H)=1`, equivalently whether `f` is squarefree.
    #[must_use]
    pub fn is_squarefree(&self) -> bool {
        self.component_gcd == Gf2Poly::one()
    }

    /// Whether the independently checked Rabin route proves the recursive
    /// component irreducible.
    #[must_use]
    pub const fn recursive_component_is_irreducible(&self) -> bool {
        matches!(
            self.recursive_component_irreducibility,
            Gf2IrreducibilityVerdict::Irreducible
        )
    }

    /// Whether the independently checked Rabin route proves the input
    /// polynomial irreducible.
    #[must_use]
    pub const fn polynomial_is_irreducible(&self) -> bool {
        matches!(
            self.polynomial_irreducibility,
            Gf2IrreducibilityVerdict::Irreducible
        )
    }

    /// At an odd degree, whether complement `1` and an irreducible recursive
    /// component of degree greater than one force the factor `x+1`.
    #[must_use]
    pub fn unit_complement_forces_x_plus_one(&self) -> bool {
        !self.degree.is_multiple_of(2)
            && self.complementary_component == Gf2Poly::one()
            && self
                .recursive_component
                .degree()
                .is_some_and(|value| value > 1)
            && self.recursive_component_is_irreducible()
    }
}

/// Decompose a half-degree-shaped polynomial into its Frobenius-square parity
/// components and certify the exact squarefreeness criterion.
///
/// If `f=E(x)^2+xH(x)^2`, then `f'=H(x)^2` and
///
/// ```text
/// gcd(f,f') = gcd(E,H)^2.
/// ```
///
/// Thus parity decomposition gives a smaller shaped component but does **not**
/// give an irreducibility induction: irreducibility of `f` only forces
/// coprimality of `E,H`.  Moreover, at odd degree, choosing complement `E=1`
/// with irreducible `H` of degree greater than one forces `f(1)=0`, since such
/// an `H` has no root at one and therefore `H(1)=1`.
///
/// # Errors
///
/// Rejects degrees below two, inputs without Lemire's half-degree shape, and
/// configured degree/work excess.  Every irreducibility verdict is obtained
/// from the exact Rabin route, and every positive verdict is independently
/// certificate-checked.
pub fn half_degree_parity_split_report(
    polynomial: &Gf2Poly,
    limits: Gf2Limits,
) -> Result<HalfDegreeParitySplitReport, Gf2Error> {
    let degree = polynomial.degree().ok_or(Gf2Error::NotPositiveDegree)?;
    if degree < 2 {
        return Err(Gf2Error::NotPositiveDegree);
    }
    if degree > limits.max_input_degree {
        return Err(Gf2Error::DegreeLimit {
            observed: degree,
            limit: limits.max_input_degree,
        });
    }
    if !polynomial.is_half_degree_shaped() {
        return Err(Gf2Error::InvalidCertificate(
            "parity split input is not half-degree shaped",
        ));
    }

    let mut even_exponents = Vec::new();
    let mut odd_exponents = Vec::new();
    for exponent in polynomial.exponents() {
        if exponent.is_multiple_of(2) {
            even_exponents.push(exponent / 2);
        } else {
            odd_exponents.push(exponent / 2);
        }
    }
    let even_component = Gf2Poly::from_exponents(&even_exponents, limits)?;
    let odd_component = Gf2Poly::from_exponents(&odd_exponents, limits)?;
    let (recursive_component, complementary_component) = if degree.is_multiple_of(2) {
        (even_component.clone(), odd_component.clone())
    } else {
        (odd_component.clone(), even_component.clone())
    };
    if recursive_component.degree() != Some(degree / 2)
        || !recursive_component.is_half_degree_shaped()
    {
        return Err(Gf2Error::InvalidCertificate(
            "leading parity component did not retain half-degree shape",
        ));
    }

    let mut context = Gf2Context::new(limits);
    let even_square = context.square(&even_component)?;
    let odd_square = context.square(&odd_component)?;
    let x_odd_square = context.multiply(&Gf2Poly::x(), &odd_square)?;
    let reconstructed = context.add(&even_square, &x_odd_square)?;
    if reconstructed != *polynomial {
        return Err(Gf2Error::InvalidCertificate(
            "parity components did not reconstruct the input",
        ));
    }
    let component_gcd = context.gcd(&even_component, &odd_component)?;
    let derivative_gcd = context.gcd(polynomial, &odd_square)?;
    let squared_component_gcd = context.square(&component_gcd)?;
    if derivative_gcd != squared_component_gcd {
        return Err(Gf2Error::InvalidCertificate(
            "parity-component gcd did not reconstruct gcd(f,f')",
        ));
    }
    let recursive_component_irreducibility =
        checked_irreducibility_verdict(&recursive_component, limits)?;
    let polynomial_irreducibility = checked_irreducibility_verdict(polynomial, limits)?;
    let recursive_component_is_irreducible = matches!(
        recursive_component_irreducibility,
        Gf2IrreducibilityVerdict::Irreducible
    );
    let polynomial_is_irreducible = matches!(
        polynomial_irreducibility,
        Gf2IrreducibilityVerdict::Irreducible
    );
    let unit_complement_forces_x_plus_one = !degree.is_multiple_of(2)
        && complementary_component == Gf2Poly::one()
        && recursive_component.degree().is_some_and(|value| value > 1)
        && recursive_component_is_irreducible;
    if unit_complement_forces_x_plus_one {
        let value_at_one_is_zero = polynomial.exponents().len().is_multiple_of(2);
        if !value_at_one_is_zero || polynomial_is_irreducible {
            return Err(Gf2Error::InvalidCertificate(
                "unit complement did not force the factor x+1",
            ));
        }
    }

    Ok(HalfDegreeParitySplitReport {
        degree,
        half_degree: degree / 2,
        even_component,
        odd_component,
        recursive_component,
        complementary_component,
        component_gcd,
        derivative_gcd,
        recursive_component_irreducibility,
        polynomial_irreducibility,
    })
}

fn checked_irreducibility_verdict(
    polynomial: &Gf2Poly,
    limits: Gf2Limits,
) -> Result<Gf2IrreducibilityVerdict, Gf2Error> {
    let Some(certificate) = certify_irreducible(polynomial, limits)? else {
        return Ok(Gf2IrreducibilityVerdict::Reducible);
    };
    check_irreducible_certificate(&certificate, limits)?;
    Ok(Gf2IrreducibilityVerdict::Irreducible)
}

/// Apply the characteristic-two `Q`-transform
///
/// ```text
/// Q(f)(x) = x^n f(x + x^(-1)),  n = degree(f).
/// ```
///
/// The negative powers cancel termwise, so the result lies in `GF(2)[x]`
/// and has degree `2n` when `f` is monic.  Expansion uses Lucas's theorem:
/// the nonzero terms of `(x^2+1)^i` are indexed by the submasks of `i`.
/// This operation establishes the polynomial identity only; irreducibility
/// of a transformed polynomial remains a separate certificate obligation.
///
/// # Errors
///
/// Returns a typed decline for the zero polynomial, an input or output degree
/// beyond the supplied ceilings, or a submask expansion beyond the work
/// ceiling.
pub fn characteristic_two_q_transform(
    polynomial: &Gf2Poly,
    limits: Gf2Limits,
) -> Result<Gf2Poly, Gf2Error> {
    let degree = polynomial.degree().ok_or(Gf2Error::NotPositiveDegree)?;
    if degree == 0 {
        return Err(Gf2Error::NotPositiveDegree);
    }
    if degree > limits.max_input_degree {
        return Err(Gf2Error::DegreeLimit {
            observed: degree,
            limit: limits.max_input_degree,
        });
    }
    let output_degree = degree.checked_mul(2).ok_or(Gf2Error::DegreeLimit {
        observed: usize::MAX,
        limit: limits.max_intermediate_degree,
    })?;
    if output_degree > limits.max_intermediate_degree {
        return Err(Gf2Error::DegreeLimit {
            observed: output_degree,
            limit: limits.max_intermediate_degree,
        });
    }

    let mut estimated_work = 0_u64;
    for exponent in polynomial.exponents() {
        let term_work = 1_u64.checked_shl(exponent.count_ones()).unwrap_or(u64::MAX);
        estimated_work = estimated_work.saturating_add(term_work);
        if estimated_work > limits.max_word_ops {
            return Err(Gf2Error::WorkLimit {
                used: estimated_work,
                limit: limits.max_word_ops,
            });
        }
    }

    let mut words = vec![0_u64; output_degree / 64 + 1];
    for exponent in polynomial.exponents() {
        let mut submask = exponent;
        loop {
            let output_exponent = degree - exponent + 2 * submask;
            words[output_exponent / 64] ^= 1_u64 << (output_exponent % 64);
            if submask == 0 {
                break;
            }
            submask = (submask - 1) & exponent;
        }
    }
    Ok(Gf2Poly::from_words(words))
}

/// Exact obstruction to using the standard `Q`-transform as a shaped
/// degree-doubling induction.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CharacteristicTwoQShapeObstruction {
    /// Source degree `n`.
    pub source_degree: usize,
    /// Unique constant-one source `D_n(x)+1` whose Q-transform can be shaped.
    pub unique_source: Gf2Poly,
    /// Forced shaped self-reciprocal output `x^(2n)+x^n+1`.
    pub forced_output: Gf2Poly,
    /// Whether the unique source itself has Lemire's half-degree shape.
    pub source_is_half_degree_shaped: bool,
    /// Whether the source is visibly a square because `n` is even.
    pub source_is_square: bool,
    /// Whether the structural filters leave the exceptional cubic source.
    pub cubic_is_only_possible_irreducible_source: bool,
}

/// Classify every shaped output of the standard characteristic-two
/// `Q`-transform.
///
/// A degree-`2n` Q-transform is self-reciprocal.  If it is half-degree shaped,
/// reciprocity removes all terms except degrees `0,n,2n`; irreducibility
/// forces the middle coefficient to be one.  The invariant-ring identity
///
/// ```text
/// D_n(x+x^-1)=x^n+x^-n
/// ```
///
/// then makes `D_n(x)+1` the unique possible source.  In characteristic two,
/// even `n` gives `D_n+1=(D_(n/2)+1)^2`.  For odd `n>=5`, `D_n+1` contains the
/// forbidden term `x^(n-2)`.  Thus only `n=3` survives both structural tests.
/// The operation reconstructs `D_n` by its recurrence and checks the Q-image
/// exactly; irreducibility of the exceptional cubic and sextic remains under
/// the independent Rabin checker.
///
/// # Errors
///
/// Rejects degrees below two, configured degree/work excess, or failure of the
/// exact Dickson/Q identity.
pub fn characteristic_two_q_shape_obstruction(
    source_degree: usize,
    limits: Gf2Limits,
) -> Result<CharacteristicTwoQShapeObstruction, Gf2Error> {
    if source_degree < 2 {
        return Err(Gf2Error::NotPositiveDegree);
    }
    if source_degree > limits.max_input_degree {
        return Err(Gf2Error::DegreeLimit {
            observed: source_degree,
            limit: limits.max_input_degree,
        });
    }
    let output_degree = source_degree.checked_mul(2).ok_or(Gf2Error::DegreeLimit {
        observed: usize::MAX,
        limit: limits.max_intermediate_degree,
    })?;
    if output_degree > limits.max_intermediate_degree {
        return Err(Gf2Error::DegreeLimit {
            observed: output_degree,
            limit: limits.max_intermediate_degree,
        });
    }
    let estimated_work = u64::try_from(source_degree)
        .unwrap_or(u64::MAX)
        .saturating_add(1)
        .saturating_pow(2);
    if estimated_work > limits.max_word_ops {
        return Err(Gf2Error::WorkLimit {
            used: estimated_work,
            limit: limits.max_word_ops,
        });
    }

    let mut previous_previous = Gf2Poly::zero();
    let mut previous = Gf2Poly::x();
    for degree in 2..=source_degree {
        let mut words = vec![0_u64; degree / 64 + 1];
        xor_shifted(&mut words, previous.words(), 1);
        xor_shifted(&mut words, previous_previous.words(), 0);
        previous_previous = previous;
        previous = Gf2Poly::from_words(words);
    }
    let mut source_words = previous.words().to_vec();
    source_words[0] ^= 1;
    let unique_source = Gf2Poly::from_words(source_words);
    let forced_output = Gf2Poly::from_exponents(&[0, source_degree, output_degree], limits)?;
    if characteristic_two_q_transform(&unique_source, limits)? != forced_output {
        return Err(Gf2Error::InvalidCertificate(
            "Dickson source does not reconstruct the forced shaped Q-output",
        ));
    }
    let source_is_half_degree_shaped = unique_source.is_half_degree_shaped();
    let source_is_square = source_degree.is_multiple_of(2);
    Ok(CharacteristicTwoQShapeObstruction {
        source_degree,
        unique_source,
        forced_output,
        source_is_half_degree_shaped,
        source_is_square,
        cubic_is_only_possible_irreducible_source: source_degree == 3,
    })
}

/// Exact obstruction to repairing a quadratic Artin--Schreier composition by
/// a binary projective change of variable.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CharacteristicTwoProjectiveDoublingObstruction {
    /// Odd source degree `n` and half of the doubled output degree.
    pub source_degree: usize,
    /// Doubled output degree `2n`.
    pub output_degree: usize,
    /// Forbidden exponent `2n-2` forced by translation invariance.
    pub translation_forbidden_exponent: usize,
    /// Sole constant-one half-shaped candidate with inversion symmetry.
    pub inversion_candidate: Gf2Poly,
    /// Sole constant-one half-shaped candidate with transvection symmetry.
    pub transvection_candidate: Gf2Poly,
    /// Explicit factor `x^2+x+1` of the transvection candidate.
    pub transvection_factor: Gf2Poly,
    /// Whether the inversion candidate is the already classified shaped
    /// self-reciprocal Q-transform output.
    pub inversion_candidate_is_q_output: bool,
    /// Whether the three projective involution classes leave no new universal
    /// shaped doubling construction.
    pub closes_new_projective_doubling_route: bool,
}

/// Classify half-shaped degree doublings stabilized by an involution in
/// `PGL_2(GF(2))`.
///
/// A separable quadratic Artin--Schreier composition is invariant under
/// `x -> x+1`.  Conjugating by any binary projective change of variable makes
/// its output invariant under one of the three involutions
///
/// ```text
/// x -> x+1,  x -> 1/x,  x -> x/(x+1).
/// ```
///
/// For odd `n>=3`, translation invariance is incompatible with half-shape:
/// `(x+1)^(2n)+x^(2n)` has an uncancellable term in degree `2n-2>n`.
/// Inversion symmetry leaves only `x^(2n)+x^n+1` after the reducible square
/// `x^(2n)+1` is removed.  This is exactly the Q-transform/cyclotomic
/// candidate already classified by [`characteristic_two_q_shape_obstruction`].
/// Finally, reciprocating a transvection-invariant half-shaped polynomial
/// turns it into a translation invariant polynomial with no terms in degrees
/// `1..n-1`.  Since the invariant ring is `GF(2)[x^2+x]`, its only
/// constant-one possibility is
///
/// ```text
/// x^(2n)+(x+1)^n,
/// ```
///
/// which is divisible by `x^2+x+1`: at a nontrivial cube root `w`,
/// `w+1=w^2`, so the two summands agree.  Thus projective repair yields only
/// the already known self-reciprocal family or a reducible polynomial, not a
/// universal doubling induction.
///
/// # Errors
///
/// Rejects even degrees and odd degrees below three, configured degree/work
/// excess, or failure of either exact polynomial identity.
pub fn characteristic_two_projective_doubling_obstruction(
    source_degree: usize,
    limits: Gf2Limits,
) -> Result<CharacteristicTwoProjectiveDoublingObstruction, Gf2Error> {
    if source_degree < 3 || source_degree.is_multiple_of(2) {
        return Err(Gf2Error::NotPositiveDegree);
    }
    if source_degree > limits.max_input_degree {
        return Err(Gf2Error::DegreeLimit {
            observed: source_degree,
            limit: limits.max_input_degree,
        });
    }
    let output_degree = source_degree.checked_mul(2).ok_or(Gf2Error::DegreeLimit {
        observed: usize::MAX,
        limit: limits.max_intermediate_degree,
    })?;
    if output_degree > limits.max_intermediate_degree {
        return Err(Gf2Error::DegreeLimit {
            observed: output_degree,
            limit: limits.max_intermediate_degree,
        });
    }
    let expansion_work = 1_u64
        .checked_shl(source_degree.count_ones())
        .unwrap_or(u64::MAX);
    if expansion_work > limits.max_word_ops {
        return Err(Gf2Error::WorkLimit {
            used: expansion_work,
            limit: limits.max_word_ops,
        });
    }

    let translation_forbidden_exponent = output_degree - 2;
    if translation_forbidden_exponent <= source_degree {
        return Err(Gf2Error::InvalidCertificate(
            "translation obstruction does not lie above the half-degree cutoff",
        ));
    }
    let inversion_candidate = Gf2Poly::from_exponents(&[0, source_degree, output_degree], limits)?;
    let q_report = characteristic_two_q_shape_obstruction(source_degree, limits)?;
    let inversion_candidate_is_q_output = inversion_candidate == q_report.forced_output;
    if !inversion_candidate_is_q_output {
        return Err(Gf2Error::InvalidCertificate(
            "projective inversion candidate differs from the forced Q-output",
        ));
    }

    let mut transvection_exponents = Vec::with_capacity(
        usize::try_from(expansion_work)
            .unwrap_or(usize::MAX)
            .saturating_add(1),
    );
    let mut submask = source_degree;
    loop {
        transvection_exponents.push(submask);
        if submask == 0 {
            break;
        }
        submask = (submask - 1) & source_degree;
    }
    transvection_exponents.push(output_degree);
    let transvection_candidate = Gf2Poly::from_exponents(&transvection_exponents, limits)?;
    let transvection_factor = Gf2Poly::from_exponents(&[0, 1, 2], limits)?;
    let mut context = Gf2Context::new(limits);
    let (_, remainder) = context.div_rem(&transvection_candidate, &transvection_factor)?;
    if !remainder.is_zero() {
        return Err(Gf2Error::InvalidCertificate(
            "projective transvection candidate lacks its cyclotomic factor",
        ));
    }

    Ok(CharacteristicTwoProjectiveDoublingObstruction {
        source_degree,
        output_degree,
        translation_forbidden_exponent,
        inversion_candidate,
        transvection_candidate,
        transvection_factor,
        inversion_candidate_is_q_output,
        closes_new_projective_doubling_route: true,
    })
}

/// Exact Capell criterion data for the cubic composition `f(x^3)`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CubicCompositionCriterion {
    /// Degree of the checked irreducible source polynomial.
    pub source_degree: usize,
    /// Whether the source already has Lemire's half-degree shape.
    pub source_is_half_degree_shaped: bool,
    /// The formal cubic composition `f(x^3)`.
    pub composition: Gf2Poly,
    /// `x^((2^n-1)/3) mod f` when `n` is even; absent when cubes are a
    /// permutation of `GF(2^n)`.
    pub cube_test_residue: Option<Gf2Poly>,
    /// Whether Capell's criterion proves the composition irreducible.
    pub proves_composition_irreducible: bool,
}

/// One prime-divisor test in the general monomial-composition criterion.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct MonomialCompositionPrimeTest {
    /// Prime divisor `p` of the substitution power.
    pub prime: usize,
    /// Whether `p` divides `2^n-1`, the source field's multiplicative order.
    pub divides_source_group_order: bool,
    /// `alpha^((2^n-1)/p) mod f` when the exponent is integral.
    pub power_test_residue: Option<Gf2Poly>,
    /// Whether a root `alpha` of `f` is not a `p`-th power in `GF(2^n)`.
    pub root_is_not_prime_power: bool,
}

/// Exact Capell/binomial criterion data for the composition `f(x^k)`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct MonomialCompositionCriterion {
    /// Degree of the replay-checked irreducible source.
    pub source_degree: usize,
    /// Positive substitution power `k`.
    pub power: usize,
    /// Whether the source already has Lemire's half-degree shape.
    pub source_is_half_degree_shaped: bool,
    /// The formal composition `f(x^k)`.
    pub composition: Gf2Poly,
    /// One exact non-power test for every distinct prime divisor of `k`.
    pub prime_tests: Vec<MonomialCompositionPrimeTest>,
    /// Whether the finite-field binomial criterion proves irreducibility.
    pub proves_composition_irreducible: bool,
}

/// Substitute `x^power` for `x` without changing coefficients.
///
/// # Errors
///
/// Returns a typed decline for zero `power` or an output degree beyond the
/// supplied intermediate-degree ceiling.
pub fn monomial_compose(
    polynomial: &Gf2Poly,
    power: usize,
    limits: Gf2Limits,
) -> Result<Gf2Poly, Gf2Error> {
    if power == 0 {
        return Err(Gf2Error::InvalidCertificate(
            "monomial composition power must be positive",
        ));
    }
    let Some(degree) = polynomial.degree() else {
        return Ok(Gf2Poly::zero());
    };
    let output_degree = degree.checked_mul(power).ok_or(Gf2Error::DegreeLimit {
        observed: usize::MAX,
        limit: limits.max_intermediate_degree,
    })?;
    if output_degree > limits.max_intermediate_degree {
        return Err(Gf2Error::DegreeLimit {
            observed: output_degree,
            limit: limits.max_intermediate_degree,
        });
    }
    let exponents = polynomial
        .exponents()
        .into_iter()
        .map(|exponent| exponent * power)
        .collect::<Vec<_>>();
    Gf2Poly::from_exponents(&exponents, limits)
}

fn distinct_prime_divisors(mut value: usize) -> Vec<usize> {
    let mut factors = Vec::new();
    let mut candidate = 2_usize;
    while candidate <= value / candidate {
        if value.is_multiple_of(candidate) {
            factors.push(candidate);
            while value.is_multiple_of(candidate) {
                value /= candidate;
            }
        }
        candidate = if candidate == 2 { 3 } else { candidate + 2 };
    }
    if value > 1 {
        factors.push(value);
    }
    factors
}

fn is_prime_usize(value: usize) -> bool {
    if value < 2 {
        return false;
    }
    if value.is_multiple_of(2) {
        return value == 2;
    }
    let mut divisor = 3_usize;
    while divisor <= value / divisor {
        if value.is_multiple_of(divisor) {
            return false;
        }
        divisor += 2;
    }
    true
}

fn x_power_mod_biguint(
    exponent: &BigUint,
    modulus: &Gf2Poly,
    context: &mut Gf2Context,
) -> Result<Gf2Poly, Gf2Error> {
    let mut result = Gf2Poly::one();
    for bit in (0..exponent.bits()).rev() {
        let square = context.square(&result)?;
        result = context.div_rem(&square, modulus)?.1;
        if exponent.bit(bit) {
            let product = context.multiply(&result, &Gf2Poly::x())?;
            result = context.div_rem(&product, modulus)?.1;
        }
    }
    Ok(result)
}

fn monomial_prime_test_unchecked(
    source: &Gf2Poly,
    source_degree: usize,
    prime: usize,
    context: &mut Gf2Context,
) -> Result<MonomialCompositionPrimeTest, Gf2Error> {
    let group_order = (BigUint::from(1_u8) << source_degree) - BigUint::from(1_u8);
    let prime_big = BigUint::from(prime);
    let divides_source_group_order = &group_order % &prime_big == BigUint::from(0_u8);
    let power_test_residue = if divides_source_group_order {
        let exponent = &group_order / &prime_big;
        Some(x_power_mod_biguint(&exponent, source, context)?)
    } else {
        None
    };
    let root_is_not_prime_power = power_test_residue
        .as_ref()
        .is_some_and(|residue| *residue != Gf2Poly::one());
    Ok(MonomialCompositionPrimeTest {
        prime,
        divides_source_group_order,
        power_test_residue,
        root_is_not_prime_power,
    })
}

/// Check whether a source root is not a `p`-th power in its binary field.
///
/// This is the prime-local part of [`monomial_composition_criterion`], exposed
/// separately so callers can audit large candidate rays without allocating
/// the potentially much larger formal composition.  A positive result for an
/// odd prime `p` proves that `f(x^p)` is irreducible by the same binomial and
/// Capell criterion.
///
/// # Errors
///
/// Returns a typed decline unless `prime` is prime, or when source replay or
/// bounded polynomial arithmetic fails.
pub fn monomial_prime_eligibility(
    source: &IrreducibilityCertificate,
    prime: usize,
    limits: Gf2Limits,
) -> Result<MonomialCompositionPrimeTest, Gf2Error> {
    if !is_prime_usize(prime) {
        return Err(Gf2Error::InvalidCertificate(
            "monomial eligibility divisor must be prime",
        ));
    }
    check_irreducible_certificate(source, limits)?;
    let source_degree = source
        .polynomial
        .degree()
        .ok_or(Gf2Error::NotPositiveDegree)?;
    monomial_prime_test_unchecked(
        &source.polynomial,
        source_degree,
        prime,
        &mut Gf2Context::new(limits),
    )
}

/// Check the binary finite-field binomial criterion for `f(x^k)`.
///
/// Let `f` be irreducible of degree `n`, let `alpha` be one of its roots,
/// and put `Q=2^n-1`.  The classical binomial criterion says that
/// `x^k-alpha` is irreducible over `GF(2^n)` exactly when every prime `p|k`
/// divides `ord(alpha)` but not `Q/ord(alpha)`, together with the usual
/// condition at `4|k`.  Since `Q` is odd, these conditions force `k` odd.
/// For an odd prime `p|Q`, the two order conditions are equivalently the
/// directly checkable non-power condition
///
/// ```text
/// alpha^(Q/p) != 1.
/// ```
///
/// Capell's lemma then identifies irreducibility of `x^k-alpha` with that of
/// `f(x^k)`.  Odd monomial substitution preserves Lemire's half-degree shape.
/// The source certificate is replay-checked before any conclusion is returned.
///
/// # Errors
///
/// Returns a typed decline for `k=0`, a malformed source certificate, or a
/// bounded polynomial operation that exceeds `limits`.
pub fn monomial_composition_criterion(
    source: &IrreducibilityCertificate,
    power: usize,
    limits: Gf2Limits,
) -> Result<MonomialCompositionCriterion, Gf2Error> {
    check_irreducible_certificate(source, limits)?;
    let source_degree = source
        .polynomial
        .degree()
        .ok_or(Gf2Error::NotPositiveDegree)?;
    let composition = monomial_compose(&source.polynomial, power, limits)?;
    let mut context = Gf2Context::new(limits);
    let mut prime_tests = Vec::new();
    for prime in distinct_prime_divisors(power) {
        prime_tests.push(monomial_prime_test_unchecked(
            &source.polynomial,
            source_degree,
            prime,
            &mut context,
        )?);
    }
    let proves_composition_irreducible =
        power == 1 || prime_tests.iter().all(|test| test.root_is_not_prime_power);
    Ok(MonomialCompositionCriterion {
        source_degree,
        power,
        source_is_half_degree_shaped: source.polynomial.is_half_degree_shaped(),
        composition,
        prime_tests,
        proves_composition_irreducible,
    })
}

/// Check the finite-field Capell criterion for `f(x^3)`.
///
/// The source is first replay-checked as irreducible.  If its degree `n` is
/// odd, cubing permutes `GF(2^n)` and the composition is reducible.  If `n` is
/// even, `f(x^3)` is irreducible exactly when a root `alpha` of `f` is not a
/// cube, checked by
///
/// ```text
/// alpha^((2^n-1)/3) != 1.
/// ```
///
/// Substitution by an odd power preserves the half-degree shape exactly.
/// The report establishes the criterion; callers may additionally produce a
/// Rabin certificate for the returned composition.
///
/// # Errors
///
/// Returns a typed decline if the source certificate fails or any bounded
/// polynomial operation exceeds its limits.
pub fn cubic_composition_criterion(
    source: &IrreducibilityCertificate,
    limits: Gf2Limits,
) -> Result<CubicCompositionCriterion, Gf2Error> {
    let general = monomial_composition_criterion(source, 3, limits)?;
    let cube = general
        .prime_tests
        .first()
        .ok_or(Gf2Error::InvalidCertificate(
            "cubic criterion did not emit its prime-divisor test",
        ))?;
    if cube.prime != 3 {
        return Err(Gf2Error::InvalidCertificate(
            "cubic criterion emitted the wrong prime-divisor test",
        ));
    }
    Ok(CubicCompositionCriterion {
        source_degree: general.source_degree,
        source_is_half_degree_shaped: general.source_is_half_degree_shaped,
        composition: general.composition,
        cube_test_residue: cube.power_test_residue.clone(),
        proves_composition_irreducible: general.proves_composition_irreducible,
    })
}

/// Deterministic resource ceilings for `GF(2)[x]` work.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Gf2Limits {
    /// Maximum degree of a candidate presented for irreducibility checking.
    pub max_input_degree: usize,
    /// Maximum degree of an intermediate polynomial.
    pub max_intermediate_degree: usize,
    /// Maximum number of Frobenius squarings in one certificate.
    pub max_frobenius_steps: usize,
    /// Approximate word-level work ceiling shared by an operation context.
    pub max_word_ops: u64,
}

impl Default for Gf2Limits {
    fn default() -> Self {
        Self {
            max_input_degree: 4_096,
            max_intermediate_degree: 8_192,
            max_frobenius_steps: 4_096,
            max_word_ops: 50_000_000,
        }
    }
}

/// Typed failure or bounded decline from `GF(2)[x]` work.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Gf2Error {
    /// Irreducibility is defined here only for positive-degree polynomials.
    NotPositiveDegree,
    /// Division by the zero polynomial was requested.
    DivisionByZero,
    /// A polynomial exceeded a configured degree ceiling.
    DegreeLimit {
        /// Degree that was encountered.
        observed: usize,
        /// Configured degree ceiling.
        limit: usize,
    },
    /// A certificate requires more Frobenius steps than allowed.
    FrobeniusLimit {
        /// Number of steps required by the input degree.
        observed: usize,
        /// Configured step ceiling.
        limit: usize,
    },
    /// The deterministic word-operation budget was exhausted.
    WorkLimit {
        /// Work that the attempted operation would have consumed.
        used: u64,
        /// Configured work ceiling.
        limit: u64,
    },
    /// A supplied certificate failed a structural or algebraic check.
    InvalidCertificate(&'static str),
}

impl fmt::Display for Gf2Error {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::NotPositiveDegree => write!(formatter, "polynomial has no positive degree"),
            Self::DivisionByZero => write!(formatter, "division by the zero polynomial"),
            Self::DegreeLimit { observed, limit } => {
                write!(
                    formatter,
                    "polynomial degree {observed} exceeds limit {limit}"
                )
            }
            Self::FrobeniusLimit { observed, limit } => {
                write!(formatter, "{observed} Frobenius steps exceed limit {limit}")
            }
            Self::WorkLimit { used, limit } => {
                write!(
                    formatter,
                    "word-operation count {used} exceeds limit {limit}"
                )
            }
            Self::InvalidCertificate(message) => {
                write!(formatter, "invalid certificate: {message}")
            }
        }
    }
}

impl std::error::Error for Gf2Error {}

/// A bounded arithmetic context.  Its work counter is monotone.
#[derive(Clone, Debug)]
pub struct Gf2Context {
    limits: Gf2Limits,
    word_ops: u64,
}

impl Gf2Context {
    /// Start a fresh context with the supplied ceilings.
    #[must_use]
    pub const fn new(limits: Gf2Limits) -> Self {
        Self {
            limits,
            word_ops: 0,
        }
    }

    /// Approximate word-level work charged so far.
    #[must_use]
    pub const fn word_ops(&self) -> u64 {
        self.word_ops
    }

    fn charge(&mut self, amount: usize) -> Result<(), Gf2Error> {
        let amount = u64::try_from(amount).unwrap_or(u64::MAX);
        let used = self.word_ops.saturating_add(amount);
        if used > self.limits.max_word_ops {
            return Err(Gf2Error::WorkLimit {
                used,
                limit: self.limits.max_word_ops,
            });
        }
        self.word_ops = used;
        Ok(())
    }

    fn ensure_intermediate(&self, polynomial: &Gf2Poly) -> Result<(), Gf2Error> {
        if let Some(observed) = polynomial.degree()
            && observed > self.limits.max_intermediate_degree
        {
            return Err(Gf2Error::DegreeLimit {
                observed,
                limit: self.limits.max_intermediate_degree,
            });
        }
        Ok(())
    }

    /// Add polynomials (coefficient-wise XOR).
    ///
    /// # Errors
    ///
    /// Returns a typed degree or work-limit decline.
    pub fn add(&mut self, left: &Gf2Poly, right: &Gf2Poly) -> Result<Gf2Poly, Gf2Error> {
        self.ensure_intermediate(left)?;
        self.ensure_intermediate(right)?;
        let length = left.words.len().max(right.words.len());
        self.charge(length)?;
        let mut words = vec![0; length];
        for (index, word) in words.iter_mut().enumerate() {
            *word = left.words.get(index).copied().unwrap_or(0)
                ^ right.words.get(index).copied().unwrap_or(0);
        }
        Ok(Gf2Poly::from_words(words))
    }

    /// Carryless polynomial multiplication.
    ///
    /// # Errors
    ///
    /// Returns a typed degree or work-limit decline.
    pub fn multiply(&mut self, left: &Gf2Poly, right: &Gf2Poly) -> Result<Gf2Poly, Gf2Error> {
        self.ensure_intermediate(left)?;
        self.ensure_intermediate(right)?;
        if left.is_zero() || right.is_zero() {
            return Ok(Gf2Poly::zero());
        }
        let degree = left
            .degree()
            .and_then(|value| value.checked_add(right.degree()?))
            .ok_or(Gf2Error::DegreeLimit {
                observed: usize::MAX,
                limit: self.limits.max_intermediate_degree,
            })?;
        if degree > self.limits.max_intermediate_degree {
            return Err(Gf2Error::DegreeLimit {
                observed: degree,
                limit: self.limits.max_intermediate_degree,
            });
        }
        let mut words = vec![0; degree / 64 + 1];
        for exponent in left.exponents() {
            self.charge(right.words.len().saturating_add(1))?;
            xor_shifted(&mut words, &right.words, exponent);
        }
        Ok(Gf2Poly::from_words(words))
    }

    /// Square a polynomial using characteristic-two exponent doubling.
    ///
    /// # Errors
    ///
    /// Returns a typed degree or work-limit decline.
    pub fn square(&mut self, polynomial: &Gf2Poly) -> Result<Gf2Poly, Gf2Error> {
        self.ensure_intermediate(polynomial)?;
        let Some(degree) = polynomial.degree() else {
            return Ok(Gf2Poly::zero());
        };
        let square_degree = degree.checked_mul(2).ok_or(Gf2Error::DegreeLimit {
            observed: usize::MAX,
            limit: self.limits.max_intermediate_degree,
        })?;
        if square_degree > self.limits.max_intermediate_degree {
            return Err(Gf2Error::DegreeLimit {
                observed: square_degree,
                limit: self.limits.max_intermediate_degree,
            });
        }
        let exponents = polynomial.exponents();
        self.charge(polynomial.words.len().saturating_add(exponents.len()))?;
        let mut words = vec![0; square_degree / 64 + 1];
        for exponent in exponents {
            let doubled = exponent * 2;
            words[doubled / 64] |= 1_u64 << (doubled % 64);
        }
        Ok(Gf2Poly::from_words(words))
    }

    /// Divide by a nonzero polynomial, returning `(quotient, remainder)`.
    ///
    /// # Errors
    ///
    /// Returns [`Gf2Error::DivisionByZero`] for a zero divisor, or a typed
    /// degree or work-limit decline.
    pub fn div_rem(
        &mut self,
        dividend: &Gf2Poly,
        divisor: &Gf2Poly,
    ) -> Result<(Gf2Poly, Gf2Poly), Gf2Error> {
        self.ensure_intermediate(dividend)?;
        self.ensure_intermediate(divisor)?;
        let divisor_degree = divisor.degree().ok_or(Gf2Error::DivisionByZero)?;
        let mut remainder = dividend.words.clone();
        let quotient_length = dividend
            .degree()
            .filter(|degree| *degree >= divisor_degree)
            .map_or(0, |degree| (degree - divisor_degree) / 64 + 1);
        let mut quotient = vec![0; quotient_length];
        while let Some(remainder_degree) = degree_words(&remainder) {
            if remainder_degree < divisor_degree {
                break;
            }
            let shift = remainder_degree - divisor_degree;
            quotient[shift / 64] ^= 1_u64 << (shift % 64);
            self.charge(divisor.words.len().saturating_add(1))?;
            xor_shifted(&mut remainder, &divisor.words, shift);
            trim(&mut remainder);
        }
        Ok((
            Gf2Poly::from_words(quotient),
            Gf2Poly::from_words(remainder),
        ))
    }

    /// Greatest common divisor, normalized to monic (automatic over `GF(2)`).
    ///
    /// # Errors
    ///
    /// Returns a typed degree or work-limit decline from polynomial division.
    pub fn gcd(&mut self, left: &Gf2Poly, right: &Gf2Poly) -> Result<Gf2Poly, Gf2Error> {
        let mut first = left.clone();
        let mut second = right.clone();
        while !second.is_zero() {
            let (_, remainder) = self.div_rem(&first, &second)?;
            first = second;
            second = remainder;
        }
        Ok(first)
    }

    fn extended_gcd(
        &mut self,
        left: &Gf2Poly,
        right: &Gf2Poly,
    ) -> Result<(Gf2Poly, Gf2Poly, Gf2Poly), Gf2Error> {
        let mut old_remainder = left.clone();
        let mut remainder = right.clone();
        let mut old_left = Gf2Poly::one();
        let mut left_coefficient = Gf2Poly::zero();
        let mut old_right = Gf2Poly::zero();
        let mut right_coefficient = Gf2Poly::one();

        while !remainder.is_zero() {
            let (quotient, new_remainder) = self.div_rem(&old_remainder, &remainder)?;
            old_remainder = remainder;
            remainder = new_remainder;

            let product = self.multiply(&quotient, &left_coefficient)?;
            let next = self.add(&old_left, &product)?;
            old_left = left_coefficient;
            left_coefficient = next;

            let product = self.multiply(&quotient, &right_coefficient)?;
            let next = self.add(&old_right, &product)?;
            old_right = right_coefficient;
            right_coefficient = next;
        }
        Ok((old_remainder, old_left, old_right))
    }
}

/// One checked Frobenius reduction `previous^2 = quotient*f + remainder`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct FrobeniusReduction {
    /// Quotient multiplying the candidate polynomial.
    pub quotient: Gf2Poly,
    /// Reduced residue, whose degree must be below the candidate degree.
    pub remainder: Gf2Poly,
}

/// Bezout evidence for one distinct prime divisor of the polynomial degree.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RabinBezout {
    /// A distinct prime divisor of the candidate degree.
    pub prime_divisor: usize,
    /// Coefficient of the candidate polynomial.
    pub polynomial_coefficient: Gf2Poly,
    /// Coefficient of `r_(n/p) + x`.
    pub frobenius_coefficient: Gf2Poly,
}

/// Portable polynomial-identity evidence for Rabin irreducibility.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct IrreducibilityCertificate {
    /// Candidate whose irreducibility is witnessed.
    pub polynomial: Gf2Poly,
    /// Complete chain from `x^2` through `x^(2^n)`, reduced modulo the candidate.
    pub frobenius: Vec<FrobeniusReduction>,
    /// One identity for each distinct prime divisor of the candidate degree.
    pub bezout: Vec<RabinBezout>,
}

/// Produce an irreducibility certificate, or `None` for a reducible polynomial.
///
/// Degree-one polynomials receive an empty certificate: every linear
/// polynomial over a field is irreducible.
///
/// # Errors
///
/// Returns [`Gf2Error::NotPositiveDegree`] for zero or constants, and typed
/// degree, Frobenius-step, or work-limit declines.
pub fn certify_irreducible(
    polynomial: &Gf2Poly,
    limits: Gf2Limits,
) -> Result<Option<IrreducibilityCertificate>, Gf2Error> {
    let degree = polynomial.degree().ok_or(Gf2Error::NotPositiveDegree)?;
    if degree == 0 {
        return Err(Gf2Error::NotPositiveDegree);
    }
    ensure_candidate_limits(degree, limits)?;
    if degree == 1 {
        return Ok(Some(IrreducibilityCertificate {
            polynomial: polynomial.clone(),
            frobenius: Vec::new(),
            bezout: Vec::new(),
        }));
    }

    let mut context = Gf2Context::new(limits);
    let mut current = Gf2Poly::x();
    let mut reductions = Vec::with_capacity(degree);
    let mut obligations: Vec<(usize, usize, Option<RabinBezout>)> = distinct_prime_factors(degree)
        .into_iter()
        .map(|prime| (prime, degree / prime, None))
        .collect();
    for step in 1..=degree {
        let square = context.square(&current)?;
        let (quotient, remainder) = context.div_rem(&square, polynomial)?;
        current = remainder.clone();
        reductions.push(FrobeniusReduction {
            quotient,
            remainder,
        });
        for (prime_divisor, target_step, witness) in &mut obligations {
            if *target_step != step {
                continue;
            }
            let target = context.add(&current, &Gf2Poly::x())?;
            let (gcd, polynomial_coefficient, frobenius_coefficient) =
                context.extended_gcd(polynomial, &target)?;
            if gcd != Gf2Poly::one() {
                return Ok(None);
            }
            *witness = Some(RabinBezout {
                prime_divisor: *prime_divisor,
                polynomial_coefficient,
                frobenius_coefficient,
            });
        }
    }
    if current != Gf2Poly::x() {
        return Ok(None);
    }

    let bezout = obligations
        .into_iter()
        .map(|(_, _, witness)| {
            witness.ok_or(Gf2Error::InvalidCertificate(
                "producer omitted a Rabin obligation",
            ))
        })
        .collect::<Result<Vec<_>, Gf2Error>>()?;

    Ok(Some(IrreducibilityCertificate {
        polynomial: polynomial.clone(),
        frobenius: reductions,
        bezout,
    }))
}

/// Check Rabin identity evidence without calling [`certify_irreducible`].
///
/// # Errors
///
/// Returns [`Gf2Error::InvalidCertificate`] for a failed structural or
/// polynomial-identity obligation, or a typed resource-limit decline.
pub fn check_irreducible_certificate(
    certificate: &IrreducibilityCertificate,
    limits: Gf2Limits,
) -> Result<(), Gf2Error> {
    let polynomial = &certificate.polynomial;
    let degree = polynomial.degree().ok_or(Gf2Error::NotPositiveDegree)?;
    if degree == 0 {
        return Err(Gf2Error::NotPositiveDegree);
    }
    ensure_candidate_limits(degree, limits)?;
    if degree == 1 {
        if certificate.frobenius.is_empty() && certificate.bezout.is_empty() {
            return Ok(());
        }
        return Err(Gf2Error::InvalidCertificate(
            "linear certificate must have no obligations",
        ));
    }
    if certificate.frobenius.len() != degree {
        return Err(Gf2Error::InvalidCertificate(
            "Frobenius chain length differs from the degree",
        ));
    }

    let expected_primes = distinct_prime_factors(degree);
    let supplied_primes: Vec<usize> = certificate
        .bezout
        .iter()
        .map(|witness| witness.prime_divisor)
        .collect();
    if supplied_primes != expected_primes {
        return Err(Gf2Error::InvalidCertificate(
            "Bezout obligations do not match the complete prime-divisor set",
        ));
    }

    let mut context = Gf2Context::new(limits);
    let mut current = Gf2Poly::x();
    for reduction in &certificate.frobenius {
        if reduction
            .remainder
            .degree()
            .is_some_and(|value| value >= degree)
        {
            return Err(Gf2Error::InvalidCertificate(
                "Frobenius remainder is not reduced",
            ));
        }
        let square = context.square(&current)?;
        let product = context.multiply(&reduction.quotient, polynomial)?;
        let reconstructed = context.add(&product, &reduction.remainder)?;
        if reconstructed != square {
            return Err(Gf2Error::InvalidCertificate(
                "Frobenius reduction identity does not hold",
            ));
        }
        current = reduction.remainder.clone();
    }
    if current != Gf2Poly::x() {
        return Err(Gf2Error::InvalidCertificate(
            "final Frobenius residue is not x",
        ));
    }

    for witness in &certificate.bezout {
        let residue_index = degree / witness.prime_divisor - 1;
        let residue = &certificate.frobenius[residue_index].remainder;
        let target = context.add(residue, &Gf2Poly::x())?;
        let left = context.multiply(&witness.polynomial_coefficient, polynomial)?;
        let right = context.multiply(&witness.frobenius_coefficient, &target)?;
        if context.add(&left, &right)? != Gf2Poly::one() {
            return Err(Gf2Error::InvalidCertificate(
                "Rabin Bezout identity does not equal one",
            ));
        }
    }
    Ok(())
}

fn ensure_candidate_limits(degree: usize, limits: Gf2Limits) -> Result<(), Gf2Error> {
    if degree > limits.max_input_degree {
        return Err(Gf2Error::DegreeLimit {
            observed: degree,
            limit: limits.max_input_degree,
        });
    }
    if degree > limits.max_frobenius_steps {
        return Err(Gf2Error::FrobeniusLimit {
            observed: degree,
            limit: limits.max_frobenius_steps,
        });
    }
    let required_intermediate = degree.checked_mul(2).ok_or(Gf2Error::DegreeLimit {
        observed: usize::MAX,
        limit: limits.max_intermediate_degree,
    })?;
    if required_intermediate > limits.max_intermediate_degree {
        return Err(Gf2Error::DegreeLimit {
            observed: required_intermediate,
            limit: limits.max_intermediate_degree,
        });
    }
    Ok(())
}

fn distinct_prime_factors(mut value: usize) -> Vec<usize> {
    let mut factors = Vec::new();
    let mut divisor = 2;
    while divisor <= value / divisor {
        if value.is_multiple_of(divisor) {
            factors.push(divisor);
            while value.is_multiple_of(divisor) {
                value /= divisor;
            }
        }
        divisor += if divisor == 2 { 1 } else { 2 };
    }
    if value > 1 {
        factors.push(value);
    }
    factors
}

fn degree_words(words: &[u64]) -> Option<usize> {
    let last = *words.last()?;
    let high = usize::try_from(u64::BITS - 1 - last.leading_zeros()).ok()?;
    Some((words.len() - 1) * 64 + high)
}

fn xor_shifted(target: &mut [u64], source: &[u64], shift: usize) {
    let word_shift = shift / 64;
    let bit_shift = shift % 64;
    for (index, &word) in source.iter().enumerate() {
        target[word_shift + index] ^= word << bit_shift;
        if bit_shift != 0 && word_shift + index + 1 < target.len() {
            target[word_shift + index + 1] ^= word >> (64 - bit_shift);
        }
    }
}

fn trim(words: &mut Vec<u64>) {
    while words.last() == Some(&0) {
        words.pop();
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn poly(exponents: &[usize]) -> Gf2Poly {
        Gf2Poly::from_exponents(exponents, Gf2Limits::default()).unwrap()
    }

    fn degree_u128(value: u128) -> Option<usize> {
        if value == 0 {
            None
        } else {
            usize::try_from(u128::BITS - 1 - value.leading_zeros()).ok()
        }
    }

    fn brute_remainder(mut dividend: u128, divisor: u128) -> u128 {
        let divisor_degree = degree_u128(divisor).unwrap();
        while let Some(dividend_degree) = degree_u128(dividend) {
            if dividend_degree < divisor_degree {
                break;
            }
            dividend ^= divisor << (dividend_degree - divisor_degree);
        }
        dividend
    }

    fn brute_irreducible(candidate: u128, degree: usize) -> bool {
        if degree == 1 {
            return true;
        }
        for divisor_degree in 1..=degree / 2 {
            for tail in 0..(1_u128 << divisor_degree) {
                let divisor = (1_u128 << divisor_degree) | tail;
                if brute_remainder(candidate, divisor) == 0 {
                    return false;
                }
            }
        }
        true
    }

    #[test]
    fn bit_packing_and_ring_operations_cross_word_boundaries() {
        let limits = Gf2Limits::default();
        let mut context = Gf2Context::new(limits);
        let left = poly(&[0, 1, 63, 64, 130]);
        let right = poly(&[1, 64]);
        assert_eq!(context.add(&left, &right).unwrap(), poly(&[0, 63, 130]));
        let product = context.multiply(&poly(&[0, 1]), &poly(&[0, 64])).unwrap();
        assert_eq!(product, poly(&[0, 1, 64, 65]));
        let square = context.square(&poly(&[0, 1, 65])).unwrap();
        assert_eq!(square, poly(&[0, 2, 130]));
    }

    #[test]
    fn division_reconstructs_the_dividend() {
        let mut context = Gf2Context::new(Gf2Limits::default());
        let dividend = poly(&[0, 2, 5, 70]);
        let divisor = poly(&[0, 1, 3]);
        let (quotient, remainder) = context.div_rem(&dividend, &divisor).unwrap();
        assert!(remainder.degree().is_none_or(|value| value < 3));
        let product = context.multiply(&quotient, &divisor).unwrap();
        assert_eq!(context.add(&product, &remainder).unwrap(), dividend);
    }

    #[test]
    fn certificates_agree_with_two_small_degree_oracles_through_degree_ten() {
        let limits = Gf2Limits::default();
        for degree in 1..=10 {
            for tail in 0..(1_usize << degree) {
                let bits = tail | (1_usize << degree);
                let exponents: Vec<usize> = (0..=degree)
                    .filter(|exponent| bits & (1_usize << exponent) != 0)
                    .collect();
                let candidate = poly(&exponents);
                let generic: Vec<i128> = (0..=degree)
                    .map(|exponent| i128::from(bits & (1_usize << exponent) != 0))
                    .collect();
                let expected = crate::gfp::is_irreducible(&generic, 2).unwrap();
                assert_eq!(
                    expected,
                    brute_irreducible(u128::try_from(bits).unwrap(), degree),
                    "the generic checker and independent trial division disagree for {bits:#b}"
                );
                let certificate = certify_irreducible(&candidate, limits).unwrap();
                assert_eq!(certificate.is_some(), expected, "bits={bits:#b}");
                if let Some(certificate) = certificate {
                    check_irreducible_certificate(&certificate, limits).unwrap();
                }
            }
        }
    }

    #[test]
    fn degree_400_known_witness_is_checked() {
        let limits = Gf2Limits::default();
        let candidate = poly(&[0, 2, 3, 5, 400]);
        let certificate = certify_irreducible(&candidate, limits)
            .unwrap()
            .expect("known witness must be irreducible");
        check_irreducible_certificate(&certificate, limits).unwrap();
    }

    #[test]
    fn parity_split_certifies_shape_squarefreeness_and_failed_induction() {
        let limits = Gf2Limits::default();

        // x^5+x^2+1 is irreducible, although its leading odd component is
        // x^2.  Thus irreducibility of f does not descend to the smaller
        // shaped component.
        let irreducible = poly(&[0, 2, 5]);
        let report = half_degree_parity_split_report(&irreducible, limits).unwrap();
        assert_eq!(report.degree, 5);
        assert_eq!(report.half_degree, 2);
        assert_eq!(report.even_component, poly(&[0, 1]));
        assert_eq!(report.odd_component, poly(&[2]));
        assert_eq!(report.recursive_component, poly(&[2]));
        assert_eq!(report.complementary_component, poly(&[0, 1]));
        assert_eq!(report.component_gcd, Gf2Poly::one());
        assert_eq!(report.derivative_gcd, Gf2Poly::one());
        assert!(report.is_squarefree());
        assert!(report.polynomial_is_irreducible());
        assert!(!report.recursive_component_is_irreducible());
        assert!(!report.unit_complement_forces_x_plus_one());

        // For irreducible H=x^3+x+1 and E=1, the proposed odd lift is
        // x H(x)^2+1=x^7+x^3+x+1 and has the forced root one.
        let unit_complement = poly(&[0, 1, 3, 7]);
        let report = half_degree_parity_split_report(&unit_complement, limits).unwrap();
        assert_eq!(report.recursive_component, poly(&[0, 1, 3]));
        assert_eq!(report.complementary_component, Gf2Poly::one());
        assert!(report.recursive_component_is_irreducible());
        assert!(!report.polynomial_is_irreducible());
        assert!(report.unit_complement_forces_x_plus_one());

        // The identity and squarefreeness criterion apply to even endpoints
        // as well; there the even component carries the leading term.
        let even = poly(&[0, 3, 6]);
        let report = half_degree_parity_split_report(&even, limits).unwrap();
        assert_eq!(report.even_component, poly(&[0, 3]));
        assert_eq!(report.odd_component, poly(&[1]));
        assert_eq!(report.recursive_component, report.even_component);
        assert!(report.is_squarefree());
        assert!(report.polynomial_is_irreducible());
        assert!(!report.recursive_component_is_irreducible());
    }

    #[test]
    fn parity_split_rejects_nonshaped_and_bounded_inputs() {
        let limits = Gf2Limits::default();
        assert!(matches!(
            half_degree_parity_split_report(&poly(&[0, 4, 6]), limits),
            Err(Gf2Error::InvalidCertificate(
                "parity split input is not half-degree shaped"
            ))
        ));
        assert_eq!(
            half_degree_parity_split_report(
                &poly(&[0, 2, 5]),
                Gf2Limits {
                    max_input_degree: 4,
                    ..limits
                }
            ),
            Err(Gf2Error::DegreeLimit {
                observed: 5,
                limit: 4
            })
        );
        assert_eq!(
            half_degree_parity_split_report(&Gf2Poly::one(), limits),
            Err(Gf2Error::NotPositiveDegree)
        );
    }

    #[test]
    fn characteristic_two_q_transform_separates_families_from_induction() {
        let limits = Gf2Limits::default();

        let cubic = poly(&[0, 1, 3]);
        assert!(cubic.is_half_degree_shaped());
        let sextic = characteristic_two_q_transform(&cubic, limits).unwrap();
        assert_eq!(sextic, poly(&[0, 3, 6]));
        assert!(sextic.is_half_degree_shaped());
        let sextic_certificate = certify_irreducible(&sextic, limits)
            .unwrap()
            .expect("x^6+x^3+1 is irreducible");
        check_irreducible_certificate(&sextic_certificate, limits).unwrap();

        let degree_twelve = characteristic_two_q_transform(&sextic, limits).unwrap();
        assert_eq!(degree_twelve, poly(&[0, 3, 4, 5, 6, 7, 8, 9, 12]));
        assert!(!degree_twelve.is_half_degree_shaped());

        let cyclotomic_five = poly(&[0, 1, 2, 3, 4]);
        let degree_eight = characteristic_two_q_transform(&cyclotomic_five, limits).unwrap();
        assert!(degree_eight.coefficient(7));
        assert_eq!(degree_eight.coefficient(7), cyclotomic_five.coefficient(3));
        assert!(!degree_eight.is_half_degree_shaped());
        let degree_eight_certificate = certify_irreducible(&degree_eight, limits)
            .unwrap()
            .expect("the theorem-hypothesis Q-transform is irreducible");
        check_irreducible_certificate(&degree_eight_certificate, limits).unwrap();
    }

    #[test]
    fn characteristic_two_q_transform_has_only_one_shaped_irreducible_source() {
        let limits = Gf2Limits::default();
        for degree in 2_usize..=64 {
            let report = characteristic_two_q_shape_obstruction(degree, limits).unwrap();
            assert_eq!(
                characteristic_two_q_transform(&report.unique_source, limits).unwrap(),
                report.forced_output
            );
            assert_eq!(report.source_is_square, degree.is_multiple_of(2));
            let odd_part = degree >> degree.trailing_zeros();
            assert_eq!(
                report.source_is_half_degree_shaped,
                odd_part == 1 || odd_part == 3
            );
            assert_eq!(
                report.cubic_is_only_possible_irreducible_source,
                degree == 3
            );
        }
        let cubic = characteristic_two_q_shape_obstruction(3, limits).unwrap();
        assert_eq!(cubic.unique_source, poly(&[0, 1, 3]));
        assert_eq!(cubic.forced_output, poly(&[0, 3, 6]));
        assert!(
            certify_irreducible(&cubic.unique_source, limits)
                .unwrap()
                .is_some()
        );
        assert!(
            certify_irreducible(&cubic.forced_output, limits)
                .unwrap()
                .is_some()
        );
        assert!(characteristic_two_q_shape_obstruction(1, limits).is_err());
        let tight = Gf2Limits {
            max_word_ops: 8,
            ..limits
        };
        assert!(matches!(
            characteristic_two_q_shape_obstruction(3, tight),
            Err(Gf2Error::WorkLimit { .. })
        ));
    }

    #[test]
    fn characteristic_two_q_transform_declines_before_unbounded_expansion() {
        let dense = poly(&(0..=20).collect::<Vec<_>>());
        let tight_work = Gf2Limits {
            max_word_ops: 16,
            ..Gf2Limits::default()
        };
        assert!(matches!(
            characteristic_two_q_transform(&dense, tight_work),
            Err(Gf2Error::WorkLimit { .. })
        ));

        let tight_degree = Gf2Limits {
            max_intermediate_degree: 7,
            ..Gf2Limits::default()
        };
        assert_eq!(
            characteristic_two_q_transform(&poly(&[0, 1, 4]), tight_degree),
            Err(Gf2Error::DegreeLimit {
                observed: 8,
                limit: 7
            })
        );
        assert_eq!(
            characteristic_two_q_transform(&Gf2Poly::zero(), Gf2Limits::default()),
            Err(Gf2Error::NotPositiveDegree)
        );
    }

    #[test]
    fn projective_artin_schreier_repair_collapses_to_known_or_reducible_forms() {
        let limits = Gf2Limits::default();
        for source_degree in (3_usize..=63).step_by(2) {
            let report =
                characteristic_two_projective_doubling_obstruction(source_degree, limits).unwrap();
            assert_eq!(report.output_degree, 2 * source_degree);
            assert_eq!(report.translation_forbidden_exponent, 2 * source_degree - 2);
            assert!(report.translation_forbidden_exponent > source_degree);
            assert!(report.inversion_candidate.is_half_degree_shaped());
            assert!(report.transvection_candidate.is_half_degree_shaped());
            assert!(report.inversion_candidate_is_q_output);
            assert!(report.closes_new_projective_doubling_route);

            let mut context = Gf2Context::new(limits);
            let (_, remainder) = context
                .div_rem(&report.transvection_candidate, &report.transvection_factor)
                .unwrap();
            assert!(remainder.is_zero());
        }

        let cubic = characteristic_two_projective_doubling_obstruction(3, limits).unwrap();
        assert_eq!(cubic.inversion_candidate, poly(&[0, 3, 6]));
        assert_eq!(cubic.transvection_candidate, poly(&[0, 1, 2, 3, 6]));
        assert!(characteristic_two_projective_doubling_obstruction(2, limits).is_err());
        assert!(characteristic_two_projective_doubling_obstruction(4, limits).is_err());

        let tight = Gf2Limits {
            max_word_ops: 3,
            ..limits
        };
        assert!(matches!(
            characteristic_two_projective_doubling_obstruction(3, tight),
            Err(Gf2Error::WorkLimit { .. })
        ));
    }

    #[test]
    fn cubic_capell_criterion_builds_shaped_irreducible_families() {
        let limits = Gf2Limits::default();

        let quadratic = certify_irreducible(&poly(&[0, 1, 2]), limits)
            .unwrap()
            .unwrap();
        let first = cubic_composition_criterion(&quadratic, limits).unwrap();
        assert!(first.source_is_half_degree_shaped);
        assert_eq!(first.cube_test_residue, Some(poly(&[1])));
        assert!(first.proves_composition_irreducible);
        assert_eq!(first.composition, poly(&[0, 3, 6]));
        assert!(first.composition.is_half_degree_shaped());
        let sextic = certify_irreducible(&first.composition, limits)
            .unwrap()
            .expect("Capell-positive composition must be Rabin irreducible");
        check_irreducible_certificate(&sextic, limits).unwrap();

        let second = cubic_composition_criterion(&sextic, limits).unwrap();
        assert!(second.proves_composition_irreducible);
        assert_eq!(second.composition, poly(&[0, 9, 18]));
        let degree_eighteen = certify_irreducible(&second.composition, limits)
            .unwrap()
            .expect("second cyclotomic composition must be irreducible");
        check_irreducible_certificate(&degree_eighteen, limits).unwrap();

        let primitive_quartic = certify_irreducible(&poly(&[0, 1, 4]), limits)
            .unwrap()
            .unwrap();
        let degree_twelve = cubic_composition_criterion(&primitive_quartic, limits).unwrap();
        assert!(degree_twelve.proves_composition_irreducible);
        assert_eq!(degree_twelve.composition, poly(&[0, 3, 12]));
        assert!(degree_twelve.composition.is_half_degree_shaped());
        let certificate = certify_irreducible(&degree_twelve.composition, limits)
            .unwrap()
            .expect("Capell-positive degree-twelve composition must be irreducible");
        check_irreducible_certificate(&certificate, limits).unwrap();
    }

    #[test]
    fn cubic_capell_criterion_rejects_cube_and_odd_degree_sources() {
        let limits = Gf2Limits::default();
        let cyclotomic_five = certify_irreducible(&poly(&[0, 1, 2, 3, 4]), limits)
            .unwrap()
            .unwrap();
        let cube = cubic_composition_criterion(&cyclotomic_five, limits).unwrap();
        assert_eq!(cube.cube_test_residue, Some(Gf2Poly::one()));
        assert!(!cube.proves_composition_irreducible);
        assert!(
            certify_irreducible(&cube.composition, limits)
                .unwrap()
                .is_none()
        );

        let odd = certify_irreducible(&poly(&[0, 1, 3]), limits)
            .unwrap()
            .unwrap();
        let permutation = cubic_composition_criterion(&odd, limits).unwrap();
        assert_eq!(permutation.cube_test_residue, None);
        assert!(!permutation.proves_composition_irreducible);
        assert!(
            certify_irreducible(&permutation.composition, limits)
                .unwrap()
                .is_none()
        );
    }

    #[test]
    fn general_monomial_criterion_covers_odd_and_composite_powers() {
        let limits = Gf2Limits::default();

        let cubic = certify_irreducible(&poly(&[0, 1, 3]), limits)
            .unwrap()
            .unwrap();
        let degree_twenty_one = monomial_composition_criterion(&cubic, 7, limits).unwrap();
        assert!(degree_twenty_one.source_is_half_degree_shaped);
        assert_eq!(degree_twenty_one.composition, poly(&[0, 7, 21]));
        assert_eq!(degree_twenty_one.prime_tests.len(), 1);
        assert_eq!(degree_twenty_one.prime_tests[0].prime, 7);
        assert!(degree_twenty_one.prime_tests[0].divides_source_group_order);
        assert!(degree_twenty_one.prime_tests[0].root_is_not_prime_power);
        assert!(degree_twenty_one.proves_composition_irreducible);
        assert_eq!(
            monomial_prime_eligibility(&cubic, 7, limits).unwrap(),
            degree_twenty_one.prime_tests[0]
        );
        assert!(degree_twenty_one.composition.is_half_degree_shaped());
        let certificate = certify_irreducible(&degree_twenty_one.composition, limits)
            .unwrap()
            .expect("degree-21 generalized Capell composition must be irreducible");
        check_irreducible_certificate(&certificate, limits).unwrap();

        let primitive_quartic = certify_irreducible(&poly(&[0, 1, 4]), limits)
            .unwrap()
            .unwrap();
        let composite_power =
            monomial_composition_criterion(&primitive_quartic, 15, limits).unwrap();
        assert_eq!(
            composite_power
                .prime_tests
                .iter()
                .map(|test| test.prime)
                .collect::<Vec<_>>(),
            vec![3, 5]
        );
        assert!(
            composite_power
                .prime_tests
                .iter()
                .all(|test| test.root_is_not_prime_power)
        );
        assert!(composite_power.proves_composition_irreducible);
        let certificate = certify_irreducible(&composite_power.composition, limits)
            .unwrap()
            .expect("degree-60 composite-power composition must be irreducible");
        check_irreducible_certificate(&certificate, limits).unwrap();
    }

    #[test]
    fn general_monomial_criterion_rejects_incompatible_powers() {
        let limits = Gf2Limits::default();
        let cubic = certify_irreducible(&poly(&[0, 1, 3]), limits)
            .unwrap()
            .unwrap();

        for power in [2, 3, 5] {
            let report = monomial_composition_criterion(&cubic, power, limits).unwrap();
            assert!(!report.proves_composition_irreducible);
            assert!(
                report
                    .prime_tests
                    .iter()
                    .any(|test| !test.divides_source_group_order)
            );
            assert!(
                certify_irreducible(&report.composition, limits)
                    .unwrap()
                    .is_none()
            );
        }

        let identity = monomial_composition_criterion(&cubic, 1, limits).unwrap();
        assert!(identity.prime_tests.is_empty());
        assert!(identity.proves_composition_irreducible);
        assert_eq!(identity.composition, cubic.polynomial);
        assert!(matches!(
            monomial_composition_criterion(&cubic, 0, limits),
            Err(Gf2Error::InvalidCertificate(
                "monomial composition power must be positive"
            ))
        ));
        assert!(matches!(
            monomial_prime_eligibility(&cubic, 9, limits),
            Err(Gf2Error::InvalidCertificate(
                "monomial eligibility divisor must be prime"
            ))
        ));
    }

    #[test]
    fn malformed_certificate_components_are_rejected() {
        let limits = Gf2Limits::default();
        let candidate = poly(&[0, 1, 4]);
        let certificate = certify_irreducible(&candidate, limits)
            .unwrap()
            .expect("x^4+x+1 is irreducible");

        let mut bad_remainder = certificate.clone();
        bad_remainder.frobenius[0].remainder = Gf2Poly::one();
        assert!(matches!(
            check_irreducible_certificate(&bad_remainder, limits),
            Err(Gf2Error::InvalidCertificate(_))
        ));

        let mut bad_quotient = certificate.clone();
        bad_quotient.frobenius[0].quotient = Gf2Poly::one();
        assert!(matches!(
            check_irreducible_certificate(&bad_quotient, limits),
            Err(Gf2Error::InvalidCertificate(_))
        ));

        let mut missing_prime = certificate.clone();
        missing_prime.bezout.clear();
        assert!(matches!(
            check_irreducible_certificate(&missing_prime, limits),
            Err(Gf2Error::InvalidCertificate(_))
        ));

        let mut bad_bezout = certificate;
        bad_bezout.bezout[0].polynomial_coefficient = Gf2Poly::zero();
        bad_bezout.bezout[0].frobenius_coefficient = Gf2Poly::zero();
        assert!(matches!(
            check_irreducible_certificate(&bad_bezout, limits),
            Err(Gf2Error::InvalidCertificate(_))
        ));
    }

    #[test]
    fn resource_limits_return_typed_declines() {
        let candidate = poly(&[0, 1, 20]);
        let tight_degree = Gf2Limits {
            max_input_degree: 10,
            ..Gf2Limits::default()
        };
        assert_eq!(
            certify_irreducible(&candidate, tight_degree),
            Err(Gf2Error::DegreeLimit {
                observed: 20,
                limit: 10
            })
        );

        let tight_work = Gf2Limits {
            max_word_ops: 1,
            ..Gf2Limits::default()
        };
        assert!(matches!(
            certify_irreducible(&candidate, tight_work),
            Err(Gf2Error::WorkLimit { .. })
        ));
    }
}
