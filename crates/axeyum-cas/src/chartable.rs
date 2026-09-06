//! Character tables of finite groups, exactly over the cyclotomic field
//! `ℚ(ζₘ)`, with a checker that re-derives every orthogonality relation from
//! the certificate alone.
//!
//! # What is here
//!
//! - [`Cyclotomic`], exact arithmetic in `ℚ(ζₘ)` — elements are coefficient
//!   vectors in the power basis `1, ζ, …, ζ^(φ(m)−1)`, reduced modulo the
//!   `m`-th cyclotomic polynomial, so equality is coefficientwise and needs
//!   no normalization pass. Complex conjugation is the Galois substitution
//!   `ζ ↦ ζ^(m−1)`, which is why no complex numbers appear anywhere.
//! - [`CharacterTableCertificate`], a supplied table plus the conjugacy-class
//!   data it is a table *of*, and [`CharacterTableCertificate::verify`],
//!   which checks it.
//! - [`character_table_of_abelian_group`], a producer for the abelian case,
//!   where the irreducible characters are exactly the homomorphisms into the
//!   roots of unity and can be found by a bounded search over generator
//!   images. The nonabelian producer (Burnside–Dixon) is **not** here; the
//!   checker takes a table from anywhere, which is what lets the classical
//!   tables of `S₃`, `S₄`, `A₄`, `A₅`, `Q₈` and the dihedral groups be
//!   checked today.
//!
//! # What `verify` establishes, and what it does not
//!
//! It establishes, from the certificate alone:
//!
//! 1. the conjugacy classes really are the classes of the group the carried
//!    [`crate::permgroup::OrderCertificate`] describes (delegated to
//!    [`crate::permgroup::ConjugacyClassCertificate::verify`], unmodified);
//! 2. the table is square on those classes, and every entry lives in
//!    `ℚ(ζₑ)` for `e` the **recomputed** exponent of the group — not a
//!    conductor the certificate is free to pad;
//! 3. **row orthogonality**: `(1/|G|) Σₖ |Cₖ| χᵢ(gₖ) conj(χⱼ(gₖ)) = δᵢⱼ`;
//! 4. **column orthogonality**: `Σᵢ χᵢ(gₖ) conj(χᵢ(gₗ)) = δₖₗ·|G|/|Cₖ|`;
//! 5. every degree `χᵢ(1)` is a positive rational integer dividing `|G|`, and
//!    the trivial character appears exactly once;
//! 6. **Galois consistency**: for every `t` coprime to `e`, the substitution
//!    `ζ ↦ ζ^t` sends `χᵢ(g)` to `χᵢ(gᵗ)`. This is a theorem about characters
//!    that the orthogonality relations do not imply, and it is what rules out
//!    a table whose irrational entries have been permuted between columns of
//!    the same element order — the near-miss a purely metric check cannot see.
//!
//! It does **not** establish that each row is the character of an actual
//! representation. Rows 3 and 4 make the rows an orthonormal basis of the
//! class functions and rows 5 and 6 constrain them heavily, but no
//! construction of a module is checked here. A table that passes is
//! consistent with being the character table; it is not proved to be one.
//! That gap is stated rather than papered over, and it is the reason the
//! nonabelian route is a checker and the abelian route is a producer — in
//! the abelian case the rows are constructed as homomorphisms, so they are
//! characters by construction.
//!
//! # Reuse
//!
//! [`crate::permgroup::PermutationGroup::conjugacy_classes`] supplies the
//! classes and their own certificate; [`crate::permutation::Permutation`]
//! supplies composition and element order. Nothing in `permgroup.rs` or
//! `matgroup.rs` is modified. The cyclotomic arithmetic is local because the
//! crate had none: `crate::cyclotomic_polynomial` builds `Φₙ` as a symbolic
//! `CasExpr` over `i128` rationals, which is a polynomial, not a field to
//! compute in.

use std::collections::{BTreeMap, BTreeSet};

use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{Signed, Zero};

use crate::permgroup::{ConjugacyClassCertificate, PermgroupError, PermutationGroup};
use crate::permutation::Permutation;

/// The largest number of generator-image tuples
/// [`character_table_of_abelian_group`] will search before declining.
pub const ABELIAN_SEARCH_BOUND: u128 = 4_096;

// ---------------------------------------------------------------------------
// Integer polynomial helpers (for the cyclotomic polynomials)
// ---------------------------------------------------------------------------

/// `left * right`, both least-significant-coefficient first.
fn poly_mul(left: &[BigInt], right: &[BigInt]) -> Vec<BigInt> {
    if left.is_empty() || right.is_empty() {
        return Vec::new();
    }
    let mut out = vec![BigInt::from(0); left.len() + right.len() - 1];
    for (i, a) in left.iter().enumerate() {
        if a.is_zero() {
            continue;
        }
        for (j, b) in right.iter().enumerate() {
            out[i + j] += a * b;
        }
    }
    out
}

/// `numerator / divisor` where `divisor` is monic and the division is exact.
fn poly_div_monic(numerator: &[BigInt], divisor: &[BigInt]) -> Vec<BigInt> {
    let dn = divisor.len();
    if numerator.len() < dn {
        return Vec::new();
    }
    let mut rem = numerator.to_vec();
    let mut quotient = vec![BigInt::from(0); numerator.len() - dn + 1];
    for shift in (0..quotient.len()).rev() {
        let coeff = rem[shift + dn - 1].clone();
        if coeff.is_zero() {
            continue;
        }
        for (j, d) in divisor.iter().enumerate() {
            rem[shift + j] -= &coeff * d;
        }
        quotient[shift] = coeff;
    }
    quotient
}

/// The `m`-th cyclotomic polynomial, least-significant-coefficient first,
/// monic of degree `φ(m)`. Built from `xᵐ − 1 = ∏_{d | m} Φ_d`.
fn cyclotomic_polynomial_coefficients(m: u64) -> Vec<BigInt> {
    assert!(m >= 1, "the cyclotomic index is positive");
    let mut numerator = vec![BigInt::from(0); usize::try_from(m).expect("small index") + 1];
    numerator[0] = BigInt::from(-1);
    let last = numerator.len() - 1;
    numerator[last] = BigInt::from(1);
    let mut divisor = vec![BigInt::from(1)];
    for d in 1..m {
        if m % d == 0 {
            divisor = poly_mul(&divisor, &cyclotomic_polynomial_coefficients(d));
        }
    }
    poly_div_monic(&numerator, &divisor)
}

/// Euler's totient.
fn totient(m: u64) -> u64 {
    u64::try_from((1..=m).filter(|k| gcd_u64(*k, m) == 1).count()).unwrap_or(1)
}

/// A permutation's one-line image vector, as a comparable key.
/// `crate::permutation::Permutation` keeps its images private and derives no
/// `Ord`, so a map over permutations needs this.
fn image_key(p: &Permutation) -> Vec<usize> {
    (0..p.len()).map(|i| p.apply(i).expect("i < len")).collect()
}

fn gcd_u64(mut a: u64, mut b: u64) -> u64 {
    while b != 0 {
        let t = a % b;
        a = b;
        b = t;
    }
    a
}

fn lcm_u64(a: u64, b: u64) -> u64 {
    if a == 0 || b == 0 {
        return 0;
    }
    a / gcd_u64(a, b) * b
}

// ---------------------------------------------------------------------------
// Cyclotomic
// ---------------------------------------------------------------------------

/// An exact element of `ℚ(ζₘ)`, as its coordinate vector in the power basis
/// `1, ζ, …, ζ^(φ(m)−1)` reduced modulo `Φₘ`.
///
/// Two elements are equal exactly when their coefficient vectors are, because
/// the power basis is a ℚ-basis of the field — there is no normalization step
/// and no floating point anywhere.
///
/// ```
/// use axeyum_cas::chartable::Cyclotomic;
/// // 1 + ζ₅ + ζ₅⁴ is the golden ratio (1 + √5)/2, and it is real: equal to
/// // its own complex conjugate.
/// let phi = Cyclotomic::sum_of_roots(5, &[0, 1, 4]).unwrap();
/// assert_eq!(phi.conjugate(), phi);
/// // (φ)² = φ + 1.
/// let one = Cyclotomic::integer(5, 1).unwrap();
/// assert_eq!(phi.mul(&phi).unwrap(), phi.add(&one).unwrap());
/// ```
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct Cyclotomic {
    conductor: u64,
    coefficients: Vec<BigRational>,
}

impl Cyclotomic {
    /// The degree `φ(m)` of `ℚ(ζₘ)` over ℚ.
    fn degree(conductor: u64) -> usize {
        usize::try_from(totient(conductor)).expect("small degree")
    }

    /// `Φₘ` as rationals, least-significant first.
    fn modulus(conductor: u64) -> Vec<BigRational> {
        cyclotomic_polynomial_coefficients(conductor)
            .into_iter()
            .map(|c| BigRational::new(c, BigInt::from(1)))
            .collect()
    }

    /// Reduces a raw coefficient vector of any length modulo `Φₘ`.
    fn reduce(conductor: u64, mut raw: Vec<BigRational>) -> Cyclotomic {
        let deg = Self::degree(conductor);
        let modulus = Self::modulus(conductor);
        if raw.len() > deg {
            for i in (deg..raw.len()).rev() {
                let c = raw[i].clone();
                if c.is_zero() {
                    continue;
                }
                raw[i] = BigRational::new(BigInt::from(0), BigInt::from(1));
                for j in 0..deg {
                    let delta = &c * &modulus[j];
                    raw[i - deg + j] = &raw[i - deg + j] - &delta;
                }
            }
        }
        raw.resize(deg, BigRational::new(BigInt::from(0), BigInt::from(1)));
        Cyclotomic {
            conductor,
            coefficients: raw,
        }
    }

    /// The zero of `ℚ(ζₘ)`, or `None` when `conductor == 0`.
    pub fn zero(conductor: u64) -> Option<Cyclotomic> {
        if conductor == 0 {
            return None;
        }
        Some(Self::reduce(conductor, Vec::new()))
    }

    /// The rational `numerator / denominator` inside `ℚ(ζₘ)`, or `None` when
    /// `conductor == 0` or `denominator == 0`.
    pub fn rational(conductor: u64, numerator: i64, denominator: i64) -> Option<Cyclotomic> {
        if conductor == 0 || denominator == 0 {
            return None;
        }
        Some(Self::reduce(
            conductor,
            vec![BigRational::new(
                BigInt::from(numerator),
                BigInt::from(denominator),
            )],
        ))
    }

    /// The integer `value` inside `ℚ(ζₘ)`, or `None` when `conductor == 0`.
    pub fn integer(conductor: u64, value: i64) -> Option<Cyclotomic> {
        Self::rational(conductor, value, 1)
    }

    /// `ζₘ^exponent`, for any integer exponent (reduced modulo `m` first), or
    /// `None` when `conductor == 0`.
    pub fn root_of_unity(conductor: u64, exponent: i64) -> Option<Cyclotomic> {
        if conductor == 0 {
            return None;
        }
        let m = i64::try_from(conductor).ok()?;
        let e = usize::try_from(exponent.rem_euclid(m)).ok()?;
        let mut raw = vec![BigRational::new(BigInt::from(0), BigInt::from(1)); e + 1];
        raw[e] = BigRational::new(BigInt::from(1), BigInt::from(1));
        Some(Self::reduce(conductor, raw))
    }

    /// `Σ ζₘ^e` over `exponents` — the shape every character value takes.
    ///
    /// `None` when `conductor == 0`.
    pub fn sum_of_roots(conductor: u64, exponents: &[i64]) -> Option<Cyclotomic> {
        let mut acc = Self::zero(conductor)?;
        for &e in exponents {
            acc = acc.add(&Self::root_of_unity(conductor, e)?)?;
        }
        Some(acc)
    }

    /// The conductor `m`.
    pub fn conductor(&self) -> u64 {
        self.conductor
    }

    /// The coordinate vector in the power basis.
    pub fn coefficients(&self) -> &[BigRational] {
        &self.coefficients
    }

    /// Whether this is zero.
    pub fn is_zero(&self) -> bool {
        self.coefficients.iter().all(num_traits::Zero::is_zero)
    }

    /// The rational value, when this element lies in ℚ.
    pub fn as_rational(&self) -> Option<BigRational> {
        if self
            .coefficients
            .iter()
            .skip(1)
            .all(num_traits::Zero::is_zero)
        {
            self.coefficients.first().cloned()
        } else {
            None
        }
    }

    /// Sum. `None` when the conductors differ.
    pub fn add(&self, other: &Cyclotomic) -> Option<Cyclotomic> {
        if self.conductor != other.conductor {
            return None;
        }
        Some(Cyclotomic {
            conductor: self.conductor,
            coefficients: self
                .coefficients
                .iter()
                .zip(other.coefficients.iter())
                .map(|(a, b)| a + b)
                .collect(),
        })
    }

    /// Difference. `None` when the conductors differ.
    pub fn sub(&self, other: &Cyclotomic) -> Option<Cyclotomic> {
        if self.conductor != other.conductor {
            return None;
        }
        Some(Cyclotomic {
            conductor: self.conductor,
            coefficients: self
                .coefficients
                .iter()
                .zip(other.coefficients.iter())
                .map(|(a, b)| a - b)
                .collect(),
        })
    }

    /// Product. `None` when the conductors differ.
    pub fn mul(&self, other: &Cyclotomic) -> Option<Cyclotomic> {
        if self.conductor != other.conductor {
            return None;
        }
        let n = self.coefficients.len();
        let mut raw = vec![BigRational::new(BigInt::from(0), BigInt::from(1)); 2 * n];
        for (i, a) in self.coefficients.iter().enumerate() {
            if a.is_zero() {
                continue;
            }
            for (j, b) in other.coefficients.iter().enumerate() {
                let term = a * b;
                raw[i + j] = &raw[i + j] + &term;
            }
        }
        Some(Self::reduce(self.conductor, raw))
    }

    /// Multiplication by an integer.
    pub fn scale(&self, factor: &BigInt) -> Cyclotomic {
        let f = BigRational::new(factor.clone(), BigInt::from(1));
        Cyclotomic {
            conductor: self.conductor,
            coefficients: self.coefficients.iter().map(|c| c * &f).collect(),
        }
    }

    /// The Galois substitution `ζ ↦ ζ^t`, defined exactly when `t` is coprime
    /// to the conductor; `None` otherwise.
    pub fn galois(&self, t: u64) -> Option<Cyclotomic> {
        if gcd_u64(t % self.conductor.max(1), self.conductor) != 1 {
            return None;
        }
        let mut acc = Cyclotomic::zero(self.conductor)?;
        for (k, coefficient) in self.coefficients.iter().enumerate() {
            if coefficient.is_zero() {
                continue;
            }
            let k = u64::try_from(k).ok()?;
            let exponent = i64::try_from(t.checked_mul(k)? % self.conductor).ok()?;
            let power = Cyclotomic::root_of_unity(self.conductor, exponent)?;
            let scaled = Cyclotomic {
                conductor: self.conductor,
                coefficients: power.coefficients.iter().map(|c| c * coefficient).collect(),
            };
            acc = acc.add(&scaled)?;
        }
        Some(acc)
    }

    /// Complex conjugation, which on `ℚ(ζₘ)` is `ζ ↦ ζ^(m−1) = ζ⁻¹`.
    ///
    /// # Panics
    ///
    /// Never panics: `m − 1` is always coprime to `m`.
    pub fn conjugate(&self) -> Cyclotomic {
        if self.conductor == 1 {
            return self.clone();
        }
        self.galois(self.conductor - 1)
            .expect("m - 1 is coprime to m")
    }
}

// ---------------------------------------------------------------------------
// The certificate
// ---------------------------------------------------------------------------

/// A character table, together with the conjugacy-class data it is a table
/// of, checkable on its own.
///
/// `table[i][k]` is the value of the `i`-th irreducible character at the
/// `k`-th conjugacy class, in the class order
/// [`crate::permgroup::ConjugacyClassCertificate`] fixes.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CharacterTableCertificate {
    /// The conjugacy classes of the group, with their own certificate.
    pub classes: ConjugacyClassCertificate,
    /// The conductor `m` of the field the entries live in, which must be the
    /// exponent of the group.
    pub conductor: u64,
    /// The table: one row per irreducible character, one column per class.
    pub table: Vec<Vec<Cyclotomic>>,
}

/// Why a [`CharacterTableCertificate`] failed to verify.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CharacterTableFailure {
    /// The carried conjugacy-class certificate does not itself verify.
    ClassesInvalid,
    /// The table is not square on the classes.
    NotSquare {
        /// The number of conjugacy classes.
        classes: usize,
        /// The number of rows.
        rows: usize,
    },
    /// A row has the wrong number of columns.
    RowWidthWrong {
        /// The offending row.
        row: usize,
        /// Its width.
        width: usize,
    },
    /// `conductor` is not the recomputed exponent of the group.
    ConductorIsNotTheExponent {
        /// The claimed conductor.
        claimed: u64,
        /// The exponent recomputed from the class representatives.
        exponent: u64,
    },
    /// An entry lives in a different field from `conductor`.
    EntryOutsideTheField {
        /// The offending row.
        row: usize,
        /// The offending column.
        column: usize,
    },
    /// A class is empty, or a representative's order is not computable.
    ClassRepresentativeUnusable {
        /// The offending class.
        class: usize,
    },
    /// Row orthogonality fails at this pair of characters.
    RowOrthogonalityFails {
        /// The first character.
        first: usize,
        /// The second character.
        second: usize,
    },
    /// Column orthogonality fails at this pair of classes.
    ColumnOrthogonalityFails {
        /// The first class.
        first: usize,
        /// The second class.
        second: usize,
    },
    /// No class is the singleton class of the identity.
    IdentityClassMissing,
    /// A degree is not a positive rational integer dividing the group order.
    DegreeNotADivisor {
        /// The offending row.
        row: usize,
    },
    /// The all-ones row is missing, or appears more than once.
    TrivialCharacterCount {
        /// How many all-ones rows there are.
        found: usize,
    },
    /// The Galois relation `σ_t(χ(g)) = χ(g^t)` fails.
    GaloisInconsistent {
        /// The offending row.
        row: usize,
        /// The offending class.
        class: usize,
        /// The exponent `t`.
        t: u64,
    },
    /// A class representative's power landed outside every class, so the
    /// class list is not a partition after all.
    PowerOutsideEveryClass {
        /// The offending class.
        class: usize,
        /// The exponent `t`.
        t: u64,
    },
}

/// Class data recomputed from the (already verified) class certificate.
struct ClassData {
    representatives: Vec<Permutation>,
    sizes: Vec<BigInt>,
    order: BigInt,
    exponent: u64,
    identity_class: usize,
}

fn class_data(classes: &ConjugacyClassCertificate) -> Result<ClassData, CharacterTableFailure> {
    let mut representatives = Vec::with_capacity(classes.classes.len());
    let mut sizes = Vec::with_capacity(classes.classes.len());
    let mut exponent: u64 = 1;
    for (index, class) in classes.classes.iter().enumerate() {
        let Some(first) = class.first() else {
            return Err(CharacterTableFailure::ClassRepresentativeUnusable { class: index });
        };
        let Some(order) = first.order() else {
            return Err(CharacterTableFailure::ClassRepresentativeUnusable { class: index });
        };
        let Ok(order) = u64::try_from(order) else {
            return Err(CharacterTableFailure::ClassRepresentativeUnusable { class: index });
        };
        exponent = lcm_u64(exponent, order);
        representatives.push(first.clone());
        sizes.push(BigInt::from(class.len()));
    }
    let degree = classes.group_order.degree;
    let identity = Permutation::identity(degree);
    let identity_class = classes
        .classes
        .iter()
        .position(|c| c.len() == 1 && c[0] == identity)
        .ok_or(CharacterTableFailure::IdentityClassMissing)?;
    Ok(ClassData {
        representatives,
        sizes,
        order: BigInt::from(classes.group_order.claimed_order),
        exponent,
        identity_class,
    })
}

impl CharacterTableCertificate {
    /// Re-derives every claim this certificate makes, from the certificate
    /// alone. See the module doc for the exact list, and for what the checks
    /// do *not* establish.
    ///
    /// # Errors
    ///
    /// [`CharacterTableFailure`], naming the first check that failed.
    pub fn verify(&self) -> Result<(), CharacterTableFailure> {
        if self.classes.verify().is_err() {
            return Err(CharacterTableFailure::ClassesInvalid);
        }
        let data = class_data(&self.classes)?;
        let count = self.classes.classes.len();
        if self.table.len() != count {
            return Err(CharacterTableFailure::NotSquare {
                classes: count,
                rows: self.table.len(),
            });
        }
        for (i, row) in self.table.iter().enumerate() {
            if row.len() != count {
                return Err(CharacterTableFailure::RowWidthWrong {
                    row: i,
                    width: row.len(),
                });
            }
        }
        if self.conductor != data.exponent {
            return Err(CharacterTableFailure::ConductorIsNotTheExponent {
                claimed: self.conductor,
                exponent: data.exponent,
            });
        }
        let width = Cyclotomic::degree(self.conductor);
        for (i, row) in self.table.iter().enumerate() {
            for (k, entry) in row.iter().enumerate() {
                if entry.conductor != self.conductor || entry.coefficients.len() != width {
                    return Err(CharacterTableFailure::EntryOutsideTheField { row: i, column: k });
                }
            }
        }
        self.check_row_orthogonality(&data)?;
        self.check_column_orthogonality(&data)?;
        self.check_degrees_and_trivial_row(&data)?;
        self.check_galois(&data)
    }

    fn check_row_orthogonality(&self, data: &ClassData) -> Result<(), CharacterTableFailure> {
        let count = self.table.len();
        for i in 0..count {
            for j in i..count {
                let mut acc = Cyclotomic::zero(self.conductor)
                    .expect("conductor is positive by construction");
                for k in 0..count {
                    let term = self.table[i][k]
                        .mul(&self.table[j][k].conjugate())
                        .expect("conductors were checked equal")
                        .scale(&data.sizes[k]);
                    acc = acc.add(&term).expect("same conductor");
                }
                let want = if i == j {
                    data.order.clone()
                } else {
                    BigInt::from(0)
                };
                if acc.as_rational() != Some(BigRational::new(want, BigInt::from(1))) {
                    return Err(CharacterTableFailure::RowOrthogonalityFails {
                        first: i,
                        second: j,
                    });
                }
            }
        }
        Ok(())
    }

    fn check_column_orthogonality(&self, data: &ClassData) -> Result<(), CharacterTableFailure> {
        let count = self.table.len();
        for k in 0..count {
            for l in k..count {
                let mut acc = Cyclotomic::zero(self.conductor)
                    .expect("conductor is positive by construction");
                for row in &self.table {
                    let term = row[k]
                        .mul(&row[l].conjugate())
                        .expect("conductors were checked equal");
                    acc = acc.add(&term).expect("same conductor");
                }
                // The centralizer order |G| / |C_k| -- exact because every
                // class size divides the group order (checked by the class
                // certificate's own class equation).
                let want = if k == l {
                    BigRational::new(data.order.clone(), data.sizes[k].clone())
                } else {
                    BigRational::new(BigInt::from(0), BigInt::from(1))
                };
                if acc.as_rational() != Some(want) {
                    return Err(CharacterTableFailure::ColumnOrthogonalityFails {
                        first: k,
                        second: l,
                    });
                }
            }
        }
        Ok(())
    }

    fn check_degrees_and_trivial_row(&self, data: &ClassData) -> Result<(), CharacterTableFailure> {
        let one = Cyclotomic::integer(self.conductor, 1).expect("conductor is positive");
        let mut trivial_rows = 0usize;
        for (i, row) in self.table.iter().enumerate() {
            let Some(degree) = row[data.identity_class].as_rational() else {
                return Err(CharacterTableFailure::DegreeNotADivisor { row: i });
            };
            if !degree.is_integer()
                || !degree.is_positive()
                || (&data.order % degree.numer()) != BigInt::from(0)
            {
                return Err(CharacterTableFailure::DegreeNotADivisor { row: i });
            }
            if row.iter().all(|entry| *entry == one) {
                trivial_rows += 1;
            }
        }
        if trivial_rows != 1 {
            return Err(CharacterTableFailure::TrivialCharacterCount {
                found: trivial_rows,
            });
        }
        Ok(())
    }

    fn check_galois(&self, data: &ClassData) -> Result<(), CharacterTableFailure> {
        // `t` coprime to the exponent is coprime to every element order, so
        // `g -> g^t` permutes each element's own cyclic group and the
        // relation below is the standard one.
        let mut class_of: BTreeMap<Vec<usize>, usize> = BTreeMap::new();
        for (k, class) in self.classes.classes.iter().enumerate() {
            for member in class {
                class_of.insert(image_key(member), k);
            }
        }
        for t in 1..self.conductor {
            if gcd_u64(t, self.conductor) != 1 {
                continue;
            }
            for (k, representative) in data.representatives.iter().enumerate() {
                let mut power = Permutation::identity(self.classes.group_order.degree);
                for _ in 0..t {
                    power = power.compose(representative).expect("same degree");
                }
                let Some(&target) = class_of.get(&image_key(&power)) else {
                    return Err(CharacterTableFailure::PowerOutsideEveryClass { class: k, t });
                };
                for (i, row) in self.table.iter().enumerate() {
                    let Some(image) = row[k].galois(t) else {
                        return Err(CharacterTableFailure::GaloisInconsistent {
                            row: i,
                            class: k,
                            t,
                        });
                    };
                    if image != row[target] {
                        return Err(CharacterTableFailure::GaloisInconsistent {
                            row: i,
                            class: k,
                            t,
                        });
                    }
                }
            }
        }
        Ok(())
    }

    /// The degrees of the irreducible characters, in row order.
    ///
    /// `None` when a row's value at the identity is not rational, which
    /// `verify` refuses.
    pub fn degrees(&self) -> Option<Vec<BigRational>> {
        let data = class_data(&self.classes).ok()?;
        self.table
            .iter()
            .map(|row| row[data.identity_class].as_rational())
            .collect()
    }
}

// ---------------------------------------------------------------------------
// The abelian producer
// ---------------------------------------------------------------------------

/// Why [`character_table_of_abelian_group`] could not produce a table.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CharacterTableError {
    /// The group is not abelian, so its irreducible characters are not all
    /// of degree 1 and this route does not apply. The producer names the
    /// class whose size proves it.
    NotAbelian {
        /// A class with more than one element.
        class: usize,
        /// Its size.
        size: usize,
    },
    /// The conjugacy classes could not be computed (the group is past
    /// [`crate::permgroup::ENUMERATION_BOUND`]).
    Permgroup(PermgroupError),
    /// `exponent^(number of generators)` exceeds [`ABELIAN_SEARCH_BOUND`].
    SearchSpaceTooLarge {
        /// The number of tuples the search would visit.
        tuples: u128,
        /// [`ABELIAN_SEARCH_BOUND`].
        bound: u128,
    },
    /// The search found a number of characters other than the group order.
    /// A finite abelian group has exactly `|G|` of them, so this is a defect
    /// in this module rather than a fact about the input, and it is raised
    /// loudly instead of returning a short table. Never observed.
    CharacterCountWrong {
        /// The number of characters found.
        found: usize,
        /// The group order.
        order: u128,
    },
}

/// The character table of a finite **abelian** permutation group.
///
/// The irreducible characters of an abelian group are exactly its
/// homomorphisms into the roots of unity, so this searches the
/// `exponent^(generators)` assignments of a root of unity to each generator
/// and keeps the ones that extend consistently over the whole group. Every
/// row is therefore a homomorphism *by construction*, which is the gap the
/// checker alone cannot close (see the module doc).
///
/// ```
/// use axeyum_cas::chartable::character_table_of_abelian_group;
/// use axeyum_cas::permgroup::PermutationGroup;
/// use axeyum_cas::permutation::Permutation;
///
/// // The cyclic group of order 4.
/// let g = Permutation::from_cycles(&[vec![0, 1, 2, 3]], 4).unwrap();
/// let group = PermutationGroup::from_generators(vec![g], 4).unwrap();
/// let table = character_table_of_abelian_group(&group).unwrap();
/// assert_eq!(table.table.len(), 4);
/// assert!(table.verify().is_ok());
/// ```
///
/// # Errors
///
/// [`CharacterTableError`]: a nonabelian group, a group past the class
/// enumeration bound, a search space past [`ABELIAN_SEARCH_BOUND`], or the
/// unreachable count mismatch.
pub fn character_table_of_abelian_group(
    group: &PermutationGroup,
) -> Result<CharacterTableCertificate, CharacterTableError> {
    let classes = group
        .conjugacy_classes()
        .map_err(CharacterTableError::Permgroup)?;
    for (index, class) in classes.classes.iter().enumerate() {
        if class.len() != 1 {
            return Err(CharacterTableError::NotAbelian {
                class: index,
                size: class.len(),
            });
        }
    }
    // Every class is a singleton, so the class list IS the element list.
    let elements: Vec<Permutation> = classes
        .classes
        .iter()
        .map(|c| c[0].clone())
        .collect::<Vec<_>>();
    let mut exponent: u64 = 1;
    for e in &elements {
        let order = e.order().unwrap_or(0);
        let order = u64::try_from(order).unwrap_or(0);
        exponent = lcm_u64(exponent, order);
    }
    let index_of: BTreeMap<Vec<usize>, usize> = elements
        .iter()
        .enumerate()
        .map(|(i, e)| (image_key(e), i))
        .collect();
    let generators = group.generators();
    let tuples = u128::from(exponent)
        .checked_pow(u32::try_from(generators.len()).unwrap_or(u32::MAX))
        .unwrap_or(u128::MAX);
    if tuples > ABELIAN_SEARCH_BOUND {
        return Err(CharacterTableError::SearchSpaceTooLarge {
            tuples,
            bound: ABELIAN_SEARCH_BOUND,
        });
    }
    let mut rows: BTreeSet<Vec<Cyclotomic>> = BTreeSet::new();
    for code in 0..tuples {
        let mut assignment = Vec::with_capacity(generators.len());
        let mut rest = code;
        for _ in 0..generators.len() {
            assignment.push(i64::try_from(rest % u128::from(exponent)).unwrap_or(0));
            rest /= u128::from(exponent);
        }
        if let Some(row) =
            extend_to_character(exponent, &elements, &index_of, generators, &assignment)
        {
            rows.insert(row);
        }
    }
    let order = classes.group_order.claimed_order;
    if u128::try_from(rows.len()).unwrap_or(u128::MAX) != order {
        return Err(CharacterTableError::CharacterCountWrong {
            found: rows.len(),
            order,
        });
    }
    Ok(CharacterTableCertificate {
        classes,
        conductor: exponent,
        table: rows.into_iter().collect(),
    })
}

/// Assigns `ζ^assignment[i]` to `generators[i]` and propagates over the whole
/// element list. `None` when the assignment is not a homomorphism, which is
/// detected as two words reaching the same element with different values.
fn extend_to_character(
    exponent: u64,
    elements: &[Permutation],
    index_of: &BTreeMap<Vec<usize>, usize>,
    generators: &[Permutation],
    assignment: &[i64],
) -> Option<Vec<Cyclotomic>> {
    let degree = elements.first()?.len();
    let identity = Permutation::identity(degree);
    let mut values: Vec<Option<Cyclotomic>> = vec![None; elements.len()];
    let start = *index_of.get(&image_key(&identity))?;
    values[start] = Some(Cyclotomic::integer(exponent, 1)?);
    let mut frontier = vec![start];
    while let Some(current) = frontier.pop() {
        let here = values[current].clone()?;
        for (gi, g) in generators.iter().enumerate() {
            let next = elements[current].compose(g)?;
            let target = *index_of.get(&image_key(&next))?;
            let candidate = here.mul(&Cyclotomic::root_of_unity(exponent, assignment[gi])?)?;
            match &values[target] {
                Some(existing) => {
                    if *existing != candidate {
                        return None; // not well defined: not a homomorphism
                    }
                }
                None => {
                    values[target] = Some(candidate);
                    frontier.push(target);
                }
            }
        }
    }
    values.into_iter().collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    // -----------------------------------------------------------------------
    // Fixtures
    // -----------------------------------------------------------------------

    fn perm(cycles: &[Vec<usize>], n: usize) -> Permutation {
        Permutation::from_cycles(cycles, n).expect("well-formed cycles")
    }

    fn group(gens: Vec<Permutation>, degree: usize) -> PermutationGroup {
        PermutationGroup::from_generators(gens, degree).expect("well-formed generators")
    }

    /// Which class of `classes` contains `p`.
    fn column_of(classes: &[Vec<Permutation>], p: &Permutation) -> usize {
        classes
            .iter()
            .position(|c| c.contains(p))
            .unwrap_or_else(|| panic!("{p:?} should be an element of the group"))
    }

    /// Rewrites rows written in the order of `representatives` into the class
    /// order the conjugacy-class certificate fixes, so a table taken from the
    /// literature never has to guess that order.
    fn arrange(
        classes: &[Vec<Permutation>],
        representatives: &[Permutation],
        rows: &[Vec<Cyclotomic>],
    ) -> Vec<Vec<Cyclotomic>> {
        let columns: Vec<usize> = representatives
            .iter()
            .map(|r| column_of(classes, r))
            .collect();
        let mut seen: BTreeSet<usize> = BTreeSet::new();
        for &c in &columns {
            assert!(seen.insert(c), "two representatives landed in one class");
        }
        rows.iter()
            .map(|row| {
                let mut out = row.clone();
                for (i, &c) in columns.iter().enumerate() {
                    out[c] = row[i].clone();
                }
                out
            })
            .collect()
    }

    fn ints(conductor: u64, values: &[i64]) -> Vec<Cyclotomic> {
        values
            .iter()
            .map(|v| Cyclotomic::integer(conductor, *v).expect("positive conductor"))
            .collect()
    }

    /// `S₃` on three points, and the classical table
    /// (`1 1 1 / 1 -1 1 / 2 0 -1`) at `e`, a transposition, a 3-cycle.
    fn s3_table() -> CharacterTableCertificate {
        let g = group(vec![perm(&[vec![0, 1, 2]], 3), perm(&[vec![0, 1]], 3)], 3);
        let classes = g.conjugacy_classes().expect("S3 is small");
        let reps = [
            Permutation::identity(3),
            perm(&[vec![0, 1]], 3),
            perm(&[vec![0, 1, 2]], 3),
        ];
        let rows = vec![
            ints(6, &[1, 1, 1]),
            ints(6, &[1, -1, 1]),
            ints(6, &[2, 0, -1]),
        ];
        CharacterTableCertificate {
            table: arrange(&classes.classes, &reps, &rows),
            classes,
            conductor: 6,
        }
    }

    /// `S₄` on four points; the classical five-by-five table at
    /// `e, (01), (01)(23), (012), (0123)`.
    fn s4_table() -> CharacterTableCertificate {
        let g = group(
            vec![perm(&[vec![0, 1, 2, 3]], 4), perm(&[vec![0, 1]], 4)],
            4,
        );
        let classes = g.conjugacy_classes().expect("S4 is small");
        let reps = [
            Permutation::identity(4),
            perm(&[vec![0, 1]], 4),
            perm(&[vec![0, 1], vec![2, 3]], 4),
            perm(&[vec![0, 1, 2]], 4),
            perm(&[vec![0, 1, 2, 3]], 4),
        ];
        let rows = vec![
            ints(12, &[1, 1, 1, 1, 1]),
            ints(12, &[1, -1, 1, 1, -1]),
            ints(12, &[2, 0, 2, -1, 0]),
            ints(12, &[3, 1, -1, 0, -1]),
            ints(12, &[3, -1, -1, 0, 1]),
        ];
        CharacterTableCertificate {
            table: arrange(&classes.classes, &reps, &rows),
            classes,
            conductor: 12,
        }
    }

    /// `A₄`, whose table is the smallest classical one with irrational
    /// entries: the two linear characters take `ω` and `ω²` on the two
    /// three-cycle classes.
    fn a4_table() -> CharacterTableCertificate {
        let g = group(
            vec![
                perm(&[vec![0, 1, 2]], 4),
                perm(&[vec![0, 1], vec![2, 3]], 4),
            ],
            4,
        );
        let classes = g.conjugacy_classes().expect("A4 is small");
        let reps = [
            Permutation::identity(4),
            perm(&[vec![0, 1], vec![2, 3]], 4),
            perm(&[vec![0, 1, 2]], 4),
            perm(&[vec![0, 2, 1]], 4),
        ];
        // ω = ζ₃ = ζ₆², ω² = ζ₆⁴.
        let w = Cyclotomic::root_of_unity(6, 2).expect("positive conductor");
        let w2 = Cyclotomic::root_of_unity(6, 4).expect("positive conductor");
        let one = Cyclotomic::integer(6, 1).expect("positive conductor");
        let rows = vec![
            ints(6, &[1, 1, 1, 1]),
            vec![one.clone(), one.clone(), w.clone(), w2.clone()],
            vec![one.clone(), one, w2, w],
            ints(6, &[3, -1, 0, 0]),
        ];
        CharacterTableCertificate {
            table: arrange(&classes.classes, &reps, &rows),
            classes,
            conductor: 6,
        }
    }

    /// `A₅`, whose two three-dimensional characters take the golden ratio and
    /// its conjugate on the two classes of five-cycles.
    fn a5_table() -> CharacterTableCertificate {
        let g = group(
            vec![perm(&[vec![0, 1, 2, 3, 4]], 5), perm(&[vec![0, 1, 2]], 5)],
            5,
        );
        let classes = g.conjugacy_classes().expect("A5 is inside the bound");
        let reps = [
            Permutation::identity(5),
            perm(&[vec![0, 1], vec![2, 3]], 5),
            perm(&[vec![0, 1, 2]], 5),
            perm(&[vec![0, 1, 2, 3, 4]], 5),
            perm(&[vec![0, 2, 4, 1, 3]], 5),
        ];
        // (1 + √5)/2 = 1 + ζ₅ + ζ₅⁴ and (1 − √5)/2 = 1 + ζ₅² + ζ₅³, written
        // inside ℚ(ζ₃₀) since 30 is A₅'s exponent: ζ₅ = ζ₃₀⁶.
        let phi = Cyclotomic::sum_of_roots(30, &[0, 6, 24]).expect("positive conductor");
        let phi_bar = Cyclotomic::sum_of_roots(30, &[0, 12, 18]).expect("positive conductor");
        let three = Cyclotomic::integer(30, 3).expect("positive conductor");
        let minus_one = Cyclotomic::integer(30, -1).expect("positive conductor");
        let zero = Cyclotomic::zero(30).expect("positive conductor");
        let rows = vec![
            ints(30, &[1, 1, 1, 1, 1]),
            ints(30, &[4, 0, 1, -1, -1]),
            ints(30, &[5, 1, -1, 0, 0]),
            vec![
                three.clone(),
                minus_one.clone(),
                zero.clone(),
                phi.clone(),
                phi_bar.clone(),
            ],
            vec![three, minus_one, zero, phi_bar, phi],
        ];
        CharacterTableCertificate {
            table: arrange(&classes.classes, &reps, &rows),
            classes,
            conductor: 30,
        }
    }

    /// `Q₈` in its regular representation on its own eight elements, ordered
    /// `1, i, j, k, -1, -i, -j, -k`; the generators are right multiplication
    /// by `i` and by `j`.
    fn q8_group() -> PermutationGroup {
        let by_i = Permutation::from_images(vec![1, 4, 7, 2, 5, 0, 3, 6]).expect("a bijection");
        let by_j = Permutation::from_images(vec![2, 3, 4, 5, 6, 7, 0, 1]).expect("a bijection");
        group(vec![by_i, by_j], 8)
    }

    /// `Q₈`'s table: four linear characters and one of degree 2. The three
    /// two-element classes are interchangeable under relabelling, so the
    /// three sign patterns are laid down in whatever order the class
    /// certificate reports them.
    fn q8_table() -> CharacterTableCertificate {
        let g = q8_group();
        let classes = g.conjugacy_classes().expect("Q8 is small");
        let singletons: Vec<usize> = (0..classes.classes.len())
            .filter(|&k| classes.classes[k].len() == 1)
            .collect();
        let pairs: Vec<usize> = (0..classes.classes.len())
            .filter(|&k| classes.classes[k].len() == 2)
            .collect();
        assert_eq!(singletons.len(), 2, "Q8 has a two-element centre");
        assert_eq!(pairs.len(), 3, "Q8 has three classes of size two");
        let identity_column = column_of(&classes.classes, &Permutation::identity(8));
        let minus_one_column = *singletons
            .iter()
            .find(|&&k| k != identity_column)
            .expect("the other singleton is the centre's other element");
        let sign_patterns = [[1, -1, -1], [-1, 1, -1], [-1, -1, 1]];
        let mut table = Vec::new();
        table.push(ints(4, &[1, 1, 1, 1, 1]));
        for pattern in sign_patterns {
            let mut row = ints(4, &[0, 0, 0, 0, 0]);
            row[identity_column] = Cyclotomic::integer(4, 1).expect("positive conductor");
            row[minus_one_column] = Cyclotomic::integer(4, 1).expect("positive conductor");
            for (slot, &value) in pairs.iter().zip(pattern.iter()) {
                row[*slot] = Cyclotomic::integer(4, value).expect("positive conductor");
            }
            table.push(row);
        }
        let mut two = ints(4, &[0, 0, 0, 0, 0]);
        two[identity_column] = Cyclotomic::integer(4, 2).expect("positive conductor");
        two[minus_one_column] = Cyclotomic::integer(4, -2).expect("positive conductor");
        table.push(two);
        CharacterTableCertificate {
            classes,
            conductor: 4,
            table,
        }
    }

    // -----------------------------------------------------------------------
    // Cyclotomic arithmetic
    // -----------------------------------------------------------------------

    #[test]
    fn the_cyclotomic_polynomials_match_their_classical_values() {
        // Phi_1 = x - 1, Phi_2 = x + 1, Phi_4 = x^2 + 1, Phi_6 = x^2 - x + 1,
        // Phi_5 = x^4 + x^3 + x^2 + x + 1.
        let want: [(u64, Vec<i64>); 5] = [
            (1, vec![-1, 1]),
            (2, vec![1, 1]),
            (4, vec![1, 0, 1]),
            (5, vec![1, 1, 1, 1, 1]),
            (6, vec![1, -1, 1]),
        ];
        for (m, coefficients) in want {
            let got = cyclotomic_polynomial_coefficients(m);
            let expected: Vec<BigInt> = coefficients.into_iter().map(BigInt::from).collect();
            assert_eq!(got, expected, "Phi_{m}");
        }
    }

    #[test]
    fn a_primitive_root_of_unity_satisfies_its_own_minimal_polynomial() {
        for m in 1..=12u64 {
            let zeta = Cyclotomic::root_of_unity(m, 1).expect("positive conductor");
            let mut power = Cyclotomic::integer(m, 1).expect("positive conductor");
            for _ in 0..m {
                power = power.mul(&zeta).expect("same conductor");
            }
            assert_eq!(
                power,
                Cyclotomic::integer(m, 1).expect("positive conductor"),
                "zeta_{m}^{m} should be 1"
            );
        }
    }

    #[test]
    fn the_primitive_cube_root_sums_to_minus_one() {
        let w = Cyclotomic::root_of_unity(3, 1).expect("positive conductor");
        let w2 = Cyclotomic::root_of_unity(3, 2).expect("positive conductor");
        let sum = w
            .add(&w2)
            .expect("same conductor")
            .add(&Cyclotomic::integer(3, 1).expect("positive conductor"))
            .expect("same conductor");
        assert!(sum.is_zero(), "1 + w + w^2 = 0");
        assert_eq!(w.conjugate(), w2);
    }

    #[test]
    fn the_golden_ratio_lives_in_the_fifth_cyclotomic_field() {
        let phi = Cyclotomic::sum_of_roots(5, &[0, 1, 4]).expect("positive conductor");
        // Real, so fixed by conjugation.
        assert_eq!(phi.conjugate(), phi);
        // phi^2 = phi + 1.
        let one = Cyclotomic::integer(5, 1).expect("positive conductor");
        assert_eq!(
            phi.mul(&phi).expect("same conductor"),
            phi.add(&one).expect("same conductor")
        );
        // phi * conj-in-the-other-embedding = -1: phi * phi_bar = -1.
        let phi_bar = Cyclotomic::sum_of_roots(5, &[0, 2, 3]).expect("positive conductor");
        assert_eq!(
            phi.mul(&phi_bar).expect("same conductor"),
            Cyclotomic::integer(5, -1).expect("positive conductor")
        );
        // phi + phi_bar = 1.
        assert_eq!(phi.add(&phi_bar).expect("same conductor"), one);
        // The two are swapped by the Galois element zeta -> zeta^2.
        assert_eq!(phi.galois(2).expect("2 is coprime to 5"), phi_bar);
    }

    #[test]
    fn a_galois_substitution_needs_an_exponent_coprime_to_the_conductor() {
        let zeta = Cyclotomic::root_of_unity(6, 1).expect("positive conductor");
        assert!(zeta.galois(5).is_some());
        assert!(zeta.galois(2).is_none(), "2 shares a factor with 6");
        assert!(zeta.galois(3).is_none(), "3 shares a factor with 6");
    }

    // -----------------------------------------------------------------------
    // Classical tables verify
    // -----------------------------------------------------------------------

    #[test]
    fn the_s3_character_table_verifies() {
        let cert = s3_table();
        assert_eq!(cert.verify(), Ok(()));
        assert_eq!(cert.table.len(), 3);
    }

    #[test]
    fn the_s4_character_table_verifies() {
        let cert = s4_table();
        assert_eq!(cert.verify(), Ok(()));
        let degrees: Vec<BigRational> = cert.degrees().expect("rational degrees");
        let mut squares = BigInt::from(0);
        for d in &degrees {
            squares += d.numer() * d.numer();
        }
        assert_eq!(squares, BigInt::from(24), "the degrees square-sum to |S4|");
    }

    #[test]
    fn the_a4_character_table_verifies_with_its_irrational_entries() {
        let cert = a4_table();
        assert_eq!(cert.verify(), Ok(()));
        // Two entries genuinely are not rational -- otherwise this fixture
        // would be testing the rational path only.
        let irrational = cert
            .table
            .iter()
            .flatten()
            .filter(|e| e.as_rational().is_none())
            .count();
        assert_eq!(
            irrational, 4,
            "the two omega columns of the two linear rows"
        );
    }

    #[test]
    fn the_a5_character_table_verifies_with_the_golden_ratio() {
        let cert = a5_table();
        assert_eq!(cert.verify(), Ok(()));
        let irrational = cert
            .table
            .iter()
            .flatten()
            .filter(|e| e.as_rational().is_none())
            .count();
        assert_eq!(irrational, 4, "the four golden-ratio entries");
    }

    #[test]
    fn the_q8_character_table_verifies() {
        let cert = q8_table();
        assert_eq!(cert.verify(), Ok(()));
        assert_eq!(cert.classes.group_order.claimed_order, 8);
        assert_eq!(cert.table.len(), 5);
    }

    // -----------------------------------------------------------------------
    // Near-miss controls: each changes ONE thing and must be refused
    // -----------------------------------------------------------------------

    #[test]
    fn a_table_whose_two_omega_columns_are_swapped_in_one_row_is_refused() {
        let mut cert = a4_table();
        // Swapping only one row's two omega entries makes it a copy of the
        // other linear character -- an orthonormal basis it is not.
        let three_cycles: Vec<usize> = (0..cert.classes.classes.len())
            .filter(|&k| cert.classes.classes[k].len() == 4)
            .collect();
        assert_eq!(three_cycles.len(), 2);
        let row = cert
            .table
            .iter()
            .position(|r| r[three_cycles[0]].as_rational().is_none())
            .expect("a row with an omega");
        cert.table[row].swap(three_cycles[0], three_cycles[1]);
        assert!(matches!(
            cert.verify(),
            Err(CharacterTableFailure::RowOrthogonalityFails { .. })
        ));
    }

    #[test]
    fn a_table_with_the_golden_ratio_moved_to_the_involution_column_is_refused() {
        // The near-miss whose closed form is perfectly spellable: (1+sqrt 5)/2
        // is a real algebraic integer of the right size, and it is simply not
        // a character value at an element of order 2.
        let mut cert = a5_table();
        let phi = Cyclotomic::sum_of_roots(30, &[0, 6, 24]).expect("positive conductor");
        let involutions = cert
            .classes
            .classes
            .iter()
            .position(|c| c.len() == 15)
            .expect("A5 has fifteen involutions");
        let row = cert
            .table
            .iter()
            .position(|r| r.iter().any(|e| *e == phi))
            .expect("a row with the golden ratio");
        cert.table[row][involutions] = phi;
        assert!(cert.verify().is_err(), "a wrong entry must be refused");
    }

    #[test]
    fn a_table_with_one_wrong_integer_entry_is_refused() {
        let mut cert = s4_table();
        // The 2-dimensional character is 0 on transpositions; 2 is the
        // spellable wrong answer (it is the value on double transpositions).
        let transpositions = cert
            .classes
            .classes
            .iter()
            .position(|c| c.len() == 6 && c[0].order() == Some(2))
            .expect("S4 has six transpositions");
        let row = cert
            .table
            .iter()
            .position(|r| r[transpositions].is_zero())
            .expect("a row that vanishes there");
        cert.table[row][transpositions] = Cyclotomic::integer(12, 2).expect("positive conductor");
        assert!(matches!(
            cert.verify(),
            Err(CharacterTableFailure::RowOrthogonalityFails { .. })
        ));
    }

    #[test]
    fn a_padded_conductor_is_refused() {
        let mut cert = a5_table();
        cert.conductor = 60;
        assert_eq!(
            cert.verify(),
            Err(CharacterTableFailure::ConductorIsNotTheExponent {
                claimed: 60,
                exponent: 30
            })
        );
    }

    #[test]
    fn a_table_with_a_missing_row_is_refused() {
        let mut cert = s3_table();
        cert.table.pop();
        assert_eq!(
            cert.verify(),
            Err(CharacterTableFailure::NotSquare {
                classes: 3,
                rows: 2
            })
        );
    }

    #[test]
    fn a_table_with_a_short_row_is_refused() {
        let mut cert = s3_table();
        cert.table[1].pop();
        assert_eq!(
            cert.verify(),
            Err(CharacterTableFailure::RowWidthWrong { row: 1, width: 2 })
        );
    }

    #[test]
    fn a_table_with_a_negated_row_is_refused_by_the_degree_check_alone() {
        // Negating a WHOLE row leaves both orthogonality relations exactly
        // where they were (every inner product involving that row picks up
        // either two sign flips or one, and the one-flip cases are all zero),
        // leaves the trivial-row count alone, and stays Galois-consistent.
        // The only thing wrong with it is that a character's degree is
        // positive -- so this fixture is what isolates that guard. Negating
        // the degree ALONE does not: it breaks row orthogonality first.
        let mut cert = s3_table();
        let identity_column = column_of(&cert.classes.classes, &Permutation::identity(3));
        let row = cert
            .table
            .iter()
            .position(|r| r[identity_column] == Cyclotomic::integer(6, 2).expect("conductor"))
            .expect("the two-dimensional row");
        let negated: Vec<Cyclotomic> = cert.table[row]
            .iter()
            .map(|e| {
                Cyclotomic::zero(6)
                    .expect("conductor")
                    .sub(e)
                    .expect("same conductor")
            })
            .collect();
        cert.table[row] = negated;
        let data = class_data(&cert.classes).expect("classes are usable");
        assert_eq!(cert.check_row_orthogonality(&data), Ok(()));
        assert_eq!(cert.check_column_orthogonality(&data), Ok(()));
        assert_eq!(cert.check_galois(&data), Ok(()));
        assert_eq!(
            cert.verify(),
            Err(CharacterTableFailure::DegreeNotADivisor { row })
        );
    }

    #[test]
    fn a_table_with_two_trivial_rows_is_refused() {
        let mut cert = s3_table();
        // Replace the sign character with a second copy of the trivial one.
        // Row orthogonality goes first, which is the honest answer: the
        // duplicate breaks the basis before the trivial-row count is reached.
        let trivial = cert
            .table
            .iter()
            .find(|r| {
                r.iter()
                    .all(|e| *e == Cyclotomic::integer(6, 1).expect("conductor"))
            })
            .expect("the trivial row")
            .clone();
        cert.table[1] = trivial;
        assert!(cert.verify().is_err());
    }

    #[test]
    fn a_table_whose_classes_are_not_the_groups_classes_is_refused() {
        let mut cert = s3_table();
        // Merge two classes: the class certificate's own partition check
        // fires before anything in this module looks at the table.
        let merged = cert.classes.classes.remove(2);
        cert.classes.classes[1].extend(merged);
        assert_eq!(cert.verify(), Err(CharacterTableFailure::ClassesInvalid));
    }

    #[test]
    fn a_table_whose_entries_live_in_the_wrong_field_is_refused() {
        let mut cert = s3_table();
        cert.table[0][0] = Cyclotomic::integer(12, 1).expect("positive conductor");
        assert_eq!(
            cert.verify(),
            Err(CharacterTableFailure::EntryOutsideTheField { row: 0, column: 0 })
        );
    }

    // -----------------------------------------------------------------------
    // The abelian producer
    // -----------------------------------------------------------------------

    #[test]
    fn the_cyclic_group_of_order_four_gets_its_four_linear_characters() {
        let g = group(vec![perm(&[vec![0, 1, 2, 3]], 4)], 4);
        let cert = character_table_of_abelian_group(&g).expect("C4 is abelian and small");
        assert_eq!(cert.table.len(), 4);
        assert_eq!(cert.conductor, 4);
        for degree in cert.degrees().expect("rational degrees") {
            assert_eq!(degree, BigRational::new(BigInt::from(1), BigInt::from(1)));
        }
        assert_eq!(cert.verify(), Ok(()));
    }

    #[test]
    fn the_klein_four_group_gets_a_table_of_signs() {
        let g = group(
            vec![
                perm(&[vec![0, 1], vec![2, 3]], 4),
                perm(&[vec![0, 2], vec![1, 3]], 4),
            ],
            4,
        );
        let cert = character_table_of_abelian_group(&g).expect("V4 is abelian and small");
        assert_eq!(cert.table.len(), 4);
        assert_eq!(cert.conductor, 2);
        assert_eq!(cert.verify(), Ok(()));
        // Every entry is +-1, and every row squares to the trivial one.
        for row in &cert.table {
            for entry in row {
                let value = entry.as_rational().expect("rational");
                assert_eq!(value.numer().abs(), BigInt::from(1), "entries are signs");
            }
        }
    }

    #[test]
    fn the_cyclic_group_of_order_six_gets_six_characters_over_the_sixth_field() {
        let g = group(vec![perm(&[vec![0, 1, 2, 3, 4, 5]], 6)], 6);
        let cert = character_table_of_abelian_group(&g).expect("C6 is abelian and small");
        assert_eq!(cert.table.len(), 6);
        assert_eq!(cert.conductor, 6);
        assert_eq!(cert.verify(), Ok(()));
    }

    #[test]
    fn a_product_of_two_cyclic_groups_gets_a_table_of_the_right_size() {
        // C2 x C4, order 8, on six points.
        let g = group(
            vec![perm(&[vec![0, 1]], 6), perm(&[vec![2, 3, 4, 5]], 6)],
            6,
        );
        let cert = character_table_of_abelian_group(&g).expect("abelian and small");
        assert_eq!(cert.classes.group_order.claimed_order, 8);
        assert_eq!(cert.table.len(), 8);
        assert_eq!(cert.verify(), Ok(()));
    }

    #[test]
    fn the_abelian_producer_declines_on_a_nonabelian_group() {
        let g = group(vec![perm(&[vec![0, 1, 2]], 3), perm(&[vec![0, 1]], 3)], 3);
        match character_table_of_abelian_group(&g) {
            Err(CharacterTableError::NotAbelian { size, .. }) => assert!(size > 1),
            other => panic!("expected a decline, got {other:?}"),
        }
    }

    #[test]
    fn the_abelian_producer_declines_when_the_search_space_is_too_large() {
        // The search is over `exponent^(generators)` tuples, NOT over the
        // group: C12 handed four redundant generators is an order-12 group
        // whose search space is 12^4 = 20736.
        let g12 = perm(&[(0..12).collect::<Vec<usize>>()], 12);
        let g2 = g12.compose(&g12).expect("same degree");
        let g3 = g2.compose(&g12).expect("same degree");
        let g4 = g3.compose(&g12).expect("same degree");
        let g = group(vec![g12, g2, g3, g4], 12);
        assert_eq!(g.order(), 12, "four generators, still C12");
        match character_table_of_abelian_group(&g) {
            Err(CharacterTableError::SearchSpaceTooLarge { tuples, bound }) => {
                assert_eq!(tuples, 20_736);
                assert_eq!(bound, ABELIAN_SEARCH_BOUND);
            }
            other => panic!("expected a decline, got {other:?}"),
        }
    }

    #[test]
    fn the_produced_table_of_an_abelian_group_survives_a_single_entry_change() {
        // A produced table is still checked by the same independent verifier,
        // so corrupting one entry must be caught.
        let g = group(vec![perm(&[vec![0, 1, 2, 3]], 4)], 4);
        let mut cert = character_table_of_abelian_group(&g).expect("C4 is abelian");
        assert_eq!(cert.verify(), Ok(()));
        cert.table[1][1] = Cyclotomic::integer(4, 1).expect("positive conductor");
        assert!(cert.verify().is_err());
    }

    #[test]
    fn a_column_permutation_that_is_not_a_group_automorphism_is_caught_only_by_galois() {
        // This is the fixture that ISOLATES the Galois guard, and it exists
        // because nothing else here does. Take C5's produced table and
        // transpose the columns of g and g^2, leaving the identity column and
        // the classes alone.
        //
        // Both orthogonality relations survive that untouched: every class has
        // size 1, so a row inner product is a reordering of the same five
        // terms, and a column inner product is evaluated at a bijection of the
        // columns. The degrees, the trivial row and the conductor are all
        // unmoved. But `g -> g^2` is not multiplication by a unit of Z/5, so
        // the transposition is NOT induced by an automorphism of C5, and the
        // relation sigma_t(chi(g)) = chi(g^t) breaks.
        let g = group(vec![perm(&[vec![0, 1, 2, 3, 4]], 5)], 5);
        let cert = character_table_of_abelian_group(&g).expect("C5 is abelian and small");
        assert_eq!(cert.verify(), Ok(()));

        let generator = perm(&[vec![0, 1, 2, 3, 4]], 5);
        let square = generator.compose(&generator).expect("same degree");
        let first = column_of(&cert.classes.classes, &generator);
        let second = column_of(&cert.classes.classes, &square);
        let mut swapped = cert.clone();
        for row in &mut swapped.table {
            row.swap(first, second);
        }
        assert_ne!(swapped.table, cert.table, "the swap must change something");

        // Every other check still passes, one at a time.
        let data = class_data(&swapped.classes).expect("classes are usable");
        assert_eq!(swapped.check_row_orthogonality(&data), Ok(()));
        assert_eq!(swapped.check_column_orthogonality(&data), Ok(()));
        assert_eq!(swapped.check_degrees_and_trivial_row(&data), Ok(()));
        // ...and only the Galois relation refuses it.
        assert!(matches!(
            swapped.verify(),
            Err(CharacterTableFailure::GaloisInconsistent { .. })
        ));
    }
}
