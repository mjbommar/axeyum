//! `axeyum.cas.MvPoly`, `Monomial` and `MultiPoly` — the polynomial types every
//! certificate route in this crate speaks.
//!
//! `MvPoly` arithmetic returns `None` on **`i128` coefficient overflow**. That is
//! an honest undecided, not an error (inventory §0.5), so it crosses the
//! boundary as Python `None` and never as an exception.

use std::collections::BTreeMap;

use axeyum_cas::MultiPoly as CasMultiPoly;
use axeyum_cas::mvpoly::{Monomial as CasMonomial, MvPoly as CasMvPoly};
use pyo3::prelude::*;
use pyo3::types::{PyAny, PyDict};

use crate::cas::expr::{Expr, rational_env};
use crate::cas::rational;

/// A monomial: a product of variable powers, with no coefficient.
#[pyclass(frozen, from_py_object, module = "axeyum", name = "Monomial")]
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Monomial {
    inner: CasMonomial,
}

impl Monomial {
    /// Wraps a Rust monomial.
    pub(crate) fn wrap(inner: CasMonomial) -> Self {
        Self { inner }
    }
}

#[pymethods]
impl Monomial {
    /// The empty monomial `1`.
    #[staticmethod]
    fn one() -> Monomial {
        Monomial::wrap(CasMonomial::one())
    }

    /// A monomial from `[(variable, exponent), ...]`.
    ///
    /// # Errors
    ///
    /// Propagates the per-element extraction error.
    #[staticmethod]
    fn from_powers(factors: Vec<(String, u32)>) -> Monomial {
        let borrowed: Vec<(&str, u32)> = factors
            .iter()
            .map(|(name, exponent)| (name.as_str(), *exponent))
            .collect();
        Monomial::wrap(CasMonomial::from_powers(&borrowed))
    }

    /// The sum of the exponents.
    fn total_degree(&self) -> u64 {
        self.inner.total_degree()
    }

    /// The exponent of `var`, or `0`.
    fn exponent_of(&self, var: &str) -> u32 {
        self.inner.exponent_of(var)
    }

    /// `[(variable, exponent), ...]`, collected to an owned list.
    ///
    /// The Rust iterator borrows the monomial, so it cannot cross the boundary
    /// lazily (inventory §0.3).
    fn powers(&self) -> Vec<(String, u32)> {
        self.inner
            .powers()
            .map(|(name, exponent)| (name.to_owned(), exponent))
            .collect()
    }

    fn __eq__(&self, other: &Bound<'_, PyAny>) -> bool {
        other
            .extract::<Monomial>()
            .is_ok_and(|other| other.inner == self.inner)
    }

    fn __hash__(&self) -> u64 {
        use std::hash::{Hash, Hasher};
        let mut hasher = std::collections::hash_map::DefaultHasher::new();
        self.powers().hash(&mut hasher);
        hasher.finish()
    }

    fn __repr__(&self) -> String {
        format!("Monomial({:?})", self.powers())
    }
}

/// A multivariate polynomial over the exact rationals.
#[pyclass(frozen, from_py_object, module = "axeyum", name = "MvPoly")]
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MvPoly {
    inner: CasMvPoly,
}

impl MvPoly {
    /// Wraps a Rust polynomial.
    pub(crate) fn wrap(inner: CasMvPoly) -> Self {
        Self { inner }
    }

    /// The wrapped Rust polynomial.
    pub(crate) fn inner(&self) -> &CasMvPoly {
        &self.inner
    }

    /// Wraps an optional Rust polynomial, keeping `None` as `None`.
    pub(crate) fn wrap_option(value: Option<CasMvPoly>) -> Option<Self> {
        value.map(Self::wrap)
    }

    /// Wraps a list of Rust polynomials.
    pub(crate) fn wrap_vec(values: &[CasMvPoly]) -> Vec<Self> {
        values.iter().cloned().map(Self::wrap).collect()
    }

    /// Unwraps a Python sequence of polynomials.
    ///
    /// # Errors
    ///
    /// Propagates the per-element extraction error.
    pub(crate) fn vec_from_py(values: &Bound<'_, PyAny>) -> PyResult<Vec<CasMvPoly>> {
        values
            .try_iter()?
            .map(|item| Ok(item?.extract::<MvPoly>()?.inner))
            .collect()
    }
}

#[pymethods]
impl MvPoly {
    /// The zero polynomial.
    #[staticmethod]
    fn zero() -> MvPoly {
        MvPoly::wrap(CasMvPoly::zero())
    }

    /// A constant polynomial.
    ///
    /// # Errors
    ///
    /// Raises `ValueError` when `value` is not an exact rational.
    #[staticmethod]
    fn constant(value: &Bound<'_, PyAny>) -> PyResult<MvPoly> {
        Ok(MvPoly::wrap(CasMvPoly::constant(rational::from_py(value)?)))
    }

    /// The polynomial `var`.
    #[staticmethod]
    fn var(name: &str) -> MvPoly {
        MvPoly::wrap(CasMvPoly::var(name))
    }

    /// A polynomial from `[(Monomial, coefficient), ...]`, or `None` on
    /// `i128` overflow.
    ///
    /// # Errors
    ///
    /// Raises `ValueError` when a coefficient is not an exact rational.
    #[staticmethod]
    fn from_terms(terms: &Bound<'_, PyAny>) -> PyResult<Option<MvPoly>> {
        let mut collected = Vec::new();
        for item in terms.try_iter()? {
            let (monomial, coefficient): (Monomial, Py<PyAny>) = item?.extract()?;
            let coefficient = rational::from_py(coefficient.bind(terms.py()))?;
            collected.push((monomial.inner.clone(), coefficient));
        }
        Ok(MvPoly::wrap_option(CasMvPoly::from_terms(collected)))
    }

    /// Whether every coefficient is zero.
    fn is_zero(&self) -> bool {
        self.inner.is_zero()
    }

    /// The number of nonzero terms.
    fn term_count(&self) -> usize {
        self.inner.term_count()
    }

    /// `[(Monomial, Fraction), ...]`, collected to an owned list.
    ///
    /// # Errors
    ///
    /// Propagates any Python error raised while building the fractions.
    fn terms<'py>(&self, py: Python<'py>) -> PyResult<Vec<(Monomial, Bound<'py, PyAny>)>> {
        self.inner
            .terms()
            .map(|(monomial, coefficient)| {
                Ok((
                    Monomial::wrap(monomial.clone()),
                    rational::fraction(py, *coefficient)?,
                ))
            })
            .collect()
    }

    /// The variables this polynomial mentions, sorted.
    fn variables(&self) -> Vec<String> {
        self.inner.variables().into_iter().collect()
    }

    /// The highest exponent of `var`.
    fn degree_in(&self, var: &str) -> u32 {
        self.inner.degree_in(var)
    }

    /// The highest total degree of any term.
    fn total_degree(&self) -> u64 {
        self.inner.total_degree()
    }

    /// The leading coefficient with respect to `main_var`, as a polynomial.
    fn leading_coeff(&self, main_var: &str) -> MvPoly {
        MvPoly::wrap(self.inner.leading_coeff(main_var))
    }

    /// `self + other`, or `None` on `i128` coefficient overflow.
    fn add(&self, other: &MvPoly) -> Option<MvPoly> {
        MvPoly::wrap_option(self.inner.add(&other.inner))
    }

    /// `-self`, or `None` on overflow.
    fn neg(&self) -> Option<MvPoly> {
        MvPoly::wrap_option(self.inner.neg())
    }

    /// `self - other`, or `None` on overflow.
    fn sub(&self, other: &MvPoly) -> Option<MvPoly> {
        MvPoly::wrap_option(self.inner.sub(&other.inner))
    }

    /// `self * other`, or `None` on overflow.
    fn mul(&self, other: &MvPoly) -> Option<MvPoly> {
        MvPoly::wrap_option(self.inner.mul(&other.inner))
    }

    /// `self ** exp`, or `None` on overflow.
    fn pow(&self, exp: u32) -> Option<MvPoly> {
        MvPoly::wrap_option(self.inner.pow(exp))
    }

    /// The partial derivative in `var`, or `None` on overflow.
    fn derivative_in(&self, var: &str) -> Option<MvPoly> {
        MvPoly::wrap_option(self.inner.derivative_in(var))
    }

    /// Exact evaluation under `assignment`, or `None` on an unbound variable or
    /// overflow.
    ///
    /// # Errors
    ///
    /// Raises `ValueError` when a binding is not an exact rational.
    fn evaluate<'py>(
        &self,
        py: Python<'py>,
        assignment: &Bound<'py, PyDict>,
    ) -> PyResult<Option<Bound<'py, PyAny>>> {
        let bindings: BTreeMap<String, _> = rational_env(assignment)?;
        rational::optional_fraction(py, self.inner.evaluate(&bindings))
    }

    /// `(quotient, remainder)` of division by `divisor`, or `None`.
    fn divide(&self, divisor: &MvPoly) -> Option<(MvPoly, MvPoly)> {
        self.inner
            .divide(&divisor.inner)
            .map(|(quotient, remainder)| (MvPoly::wrap(quotient), MvPoly::wrap(remainder)))
    }

    /// Whether `self` divides `other` exactly; `None` when undecided.
    fn divides(&self, other: &MvPoly) -> Option<bool> {
        self.inner.divides(&other.inner)
    }

    /// `self / divisor` when the division is exact, else `None`.
    fn exact_div(&self, divisor: &MvPoly) -> Option<MvPoly> {
        MvPoly::wrap_option(self.inner.exact_div(&divisor.inner))
    }

    /// The greatest common divisor, or `None`.
    fn gcd(&self, other: &MvPoly) -> Option<MvPoly> {
        MvPoly::wrap_option(self.inner.gcd(&other.inner))
    }

    /// The squarefree decomposition in `main_var` as `[(factor, multiplicity)]`,
    /// or `None`.
    fn squarefree(&self, main_var: &str) -> Option<Vec<(MvPoly, u32)>> {
        self.inner.squarefree(main_var).map(|factors| {
            factors
                .into_iter()
                .map(|(factor, multiplicity)| (MvPoly::wrap(factor), multiplicity))
                .collect()
        })
    }

    /// The same polynomial as an [`Expr`].
    fn to_expr(&self) -> Expr {
        Expr::wrap(self.inner.to_cas_expr())
    }

    /// The polynomial an expression denotes, or `None` when it is outside the
    /// polynomial fragment (or overflows).
    #[staticmethod]
    fn from_expr(expr: &Expr) -> Option<MvPoly> {
        MvPoly::wrap_option(CasMvPoly::from_cas_expr(expr.inner()))
    }

    /// `self + other`; **`None` on overflow**, mirroring `add`.
    fn __add__(&self, other: &MvPoly) -> Option<MvPoly> {
        self.add(other)
    }

    /// `self - other`; **`None` on overflow**, mirroring `sub`.
    fn __sub__(&self, other: &MvPoly) -> Option<MvPoly> {
        self.sub(other)
    }

    /// `self * other`; **`None` on overflow**, mirroring `mul`.
    fn __mul__(&self, other: &MvPoly) -> Option<MvPoly> {
        self.mul(other)
    }

    /// `-self`; **`None` on overflow**, mirroring `neg`.
    fn __neg__(&self) -> Option<MvPoly> {
        self.neg()
    }

    fn __eq__(&self, other: &Bound<'_, PyAny>) -> bool {
        other
            .extract::<MvPoly>()
            .is_ok_and(|other| other.inner == self.inner)
    }

    fn __repr__(&self) -> String {
        format!(
            "MvPoly(terms={}, total_degree={})",
            self.inner.term_count(),
            self.inner.total_degree()
        )
    }
}

/// The canonical polynomial normal form [`crate::cas::normalize`] produces.
///
/// Reachable only through `normalize` and through a [`crate::cas::expr::ZeroTest`]
/// witness: the Rust type has no public constructor from terms.
#[pyclass(frozen, from_py_object, module = "axeyum", name = "MultiPoly")]
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MultiPoly {
    inner: CasMultiPoly,
}

impl MultiPoly {
    /// Wraps a Rust normal form.
    pub(crate) fn wrap(inner: CasMultiPoly) -> Self {
        Self { inner }
    }

    /// Wraps an optional Rust normal form.
    pub(crate) fn wrap_option(value: Option<CasMultiPoly>) -> Option<Self> {
        value.map(Self::wrap)
    }
}

#[pymethods]
impl MultiPoly {
    /// The zero normal form.
    #[staticmethod]
    fn zero() -> MultiPoly {
        MultiPoly::wrap(CasMultiPoly::zero())
    }

    /// Whether this is the zero polynomial.
    fn is_zero(&self) -> bool {
        self.inner.is_zero()
    }

    /// The dense coefficient list in `var`, lowest degree first, or `None` when
    /// the polynomial is not univariate in `var`.
    ///
    /// # Errors
    ///
    /// Propagates any Python error raised while building the fractions.
    fn to_univariate<'py>(
        &self,
        py: Python<'py>,
        var: &str,
    ) -> PyResult<Option<Vec<Bound<'py, PyAny>>>> {
        self.inner
            .to_univariate(var)
            .map(|coefficients| {
                coefficients
                    .into_iter()
                    .map(|value| rational::fraction(py, value))
                    .collect::<PyResult<Vec<_>>>()
            })
            .transpose()
    }

    /// The same polynomial as an [`Expr`].
    fn to_expr(&self) -> Expr {
        Expr::wrap(self.inner.to_expr())
    }

    /// Exact evaluation under `env`, or `None`.
    ///
    /// # Errors
    ///
    /// Raises `ValueError` when a binding is not an exact rational.
    fn eval<'py>(
        &self,
        py: Python<'py>,
        env: &Bound<'py, PyDict>,
    ) -> PyResult<Option<Bound<'py, PyAny>>> {
        let bindings = rational_env(env)?;
        rational::optional_fraction(py, self.inner.eval(&bindings))
    }

    fn __eq__(&self, other: &Bound<'_, PyAny>) -> bool {
        other
            .extract::<MultiPoly>()
            .is_ok_and(|other| other.inner == self.inner)
    }

    fn __repr__(&self) -> String {
        format!("MultiPoly(zero={})", self.inner.is_zero())
    }
}
