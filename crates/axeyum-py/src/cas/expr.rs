//! `axeyum.cas.Expr` and the certificate-shaped values calculus returns.
//!
//! There is **no text parser** for `CasExpr` (inventory §0.1): expressions are
//! built by constructors and operators, and `__str__` renders but does not
//! round-trip. Nothing here parses a string into an expression, because the Rust
//! API has no such route to project.

use std::collections::BTreeMap;

use axeyum_cas::assumptions::{Assumptions as CasAssumptions, Sign as CasSign};
use axeyum_cas::{
    CasExpr, Certainty as CasCertainty, CertifiedIntegral as CasCertifiedIntegral,
    DefiniteIntegral as CasDefiniteIntegral, LimitPoint as CasLimitPoint, ZeroTest as CasZeroTest,
};
use axeyum_ir::Rational as IrRational;
use pyo3::exceptions::PyValueError;
use pyo3::prelude::*;
use pyo3::types::{PyAny, PyDict};

use crate::cas::poly::MultiPoly;
use crate::cas::rational;
use crate::cas::rational::RationalLike;
use crate::stub_types::PyFraction;

/// How much trust an answer carries.
///
/// `Certified` means a checkable witness is attached and the answer re-checks
/// independently; the other two do not, and collapsing them would be the exact
/// mistake this project treats as a defect.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyclass_enum(module = "axeyum._native.cas")
)]
#[pyclass(
    frozen,
    eq,
    eq_int,
    skip_from_py_object,
    module = "axeyum",
    name = "Certainty"
)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Certainty {
    /// A checkable witness is attached.
    Certified,
    /// A complete algorithm decided it, but emitted no witness.
    DecidableUncertified,
    /// May fail to find a true answer; never asserts a false one.
    Heuristic,
}

impl Certainty {
    /// Wraps the Rust tag.
    fn wrap(value: CasCertainty) -> Self {
        match value {
            CasCertainty::Certified => Certainty::Certified,
            CasCertainty::DecidableUncertified => Certainty::DecidableUncertified,
            CasCertainty::Heuristic => Certainty::Heuristic,
        }
    }
}

/// The sign an [`Assumptions`] context can establish for an expression.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyclass_enum(module = "axeyum._native.cas")
)]
#[pyclass(
    frozen,
    eq,
    eq_int,
    skip_from_py_object,
    module = "axeyum",
    name = "Sign"
)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Sign {
    /// Strictly positive.
    Positive,
    /// Strictly negative.
    Negative,
    /// Exactly zero.
    Zero,
    /// Nonnegative, not further resolved.
    Nonnegative,
    /// Nonpositive, not further resolved.
    Nonpositive,
    /// Not determined.
    Unknown,
}

impl Sign {
    /// Wraps the Rust tag.
    fn wrap(value: CasSign) -> Self {
        match value {
            CasSign::Positive => Sign::Positive,
            CasSign::Negative => Sign::Negative,
            CasSign::Zero => Sign::Zero,
            CasSign::Nonnegative => Sign::Nonnegative,
            CasSign::Nonpositive => Sign::Nonpositive,
            CasSign::Unknown => Sign::Unknown,
        }
    }
}

/// A symbolic expression.
///
/// Built only by the constructors and operators below — the crate has no parser
/// and `impl FromStr` does not exist. `str(expr)` renders the tree for humans
/// and is **not** parseable back into an `Expr`.
/// The right-hand side of an arithmetic operator: an `Expr`, a Python `int`,
/// or a `fractions.Fraction` -- the exact operands. A `float` is refused with
/// `TypeError` rather than approximated: the CAS is exact over Q, and `x + 0.5`
/// silently becoming `x + 1/2` would be a guess about the caller's intent.
struct Operand(CasExpr);

impl FromPyObject<'_, '_> for Operand {
    type Error = PyErr;

    fn extract(obj: pyo3::Borrowed<'_, '_, PyAny>) -> PyResult<Self> {
        if let Ok(expr) = obj.cast::<Expr>() {
            return Ok(Operand(expr.get().inner.clone()));
        }
        if obj.is_instance_of::<pyo3::types::PyFloat>() {
            return Err(pyo3::exceptions::PyTypeError::new_err(
                "Expr arithmetic takes Expr, int or fractions.Fraction, not float (the CAS is exact over Q; write Fraction(1, 2))",
            ));
        }
        if let Ok(n) = obj.extract::<i128>() {
            return Ok(Operand(CasExpr::int(n)));
        }
        let (num, den) = (
            obj.getattr("numerator").and_then(|v| v.extract::<i128>()),
            obj.getattr("denominator").and_then(|v| v.extract::<i128>()),
        );
        if let (Ok(num), Ok(den)) = (num, den) {
            let value = rational::checked(num, den).ok_or_else(|| {
                PyValueError::new_err(format!("{num}/{den} does not fit the i128 rational"))
            })?;
            return Ok(Operand(CasExpr::Const(value)));
        }
        Err(pyo3::exceptions::PyTypeError::new_err(format!(
            "Expr arithmetic takes Expr, int or fractions.Fraction, not {}",
            obj.get_type()
                .name()
                .map(|n| n.to_string())
                .unwrap_or_default()
        )))
    }
}

#[cfg(feature = "stub-gen")]
impl pyo3_stub_gen::PyStubType for Operand {
    fn type_input() -> pyo3_stub_gen::TypeInfo {
        use pyo3_stub_gen::PyStubType;
        <Expr as PyStubType>::type_input()
            | <i128 as PyStubType>::type_input()
            | <crate::stub_types::PyFraction<'_> as PyStubType>::type_output()
    }

    fn type_output() -> pyo3_stub_gen::TypeInfo {
        Self::type_input()
    }
}

#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyclass(module = "axeyum._native.cas")
)]
#[pyclass(frozen, from_py_object, module = "axeyum", name = "Expr")]
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Expr {
    inner: CasExpr,
}

impl Expr {
    /// Wraps a Rust expression.
    pub(crate) fn wrap(inner: CasExpr) -> Self {
        Self { inner }
    }

    /// The wrapped Rust expression.
    pub(crate) fn inner(&self) -> &CasExpr {
        &self.inner
    }

    /// Wraps an optional Rust expression, keeping `None` as `None`.
    ///
    /// A `None` here is an honest *declined or overflowed*, never an error
    /// (inventory §0.5).
    pub(crate) fn wrap_option(value: Option<CasExpr>) -> Option<Self> {
        value.map(Self::wrap)
    }

    /// Wraps a list of Rust expressions.
    pub(crate) fn wrap_vec(values: Vec<CasExpr>) -> Vec<Self> {
        values.into_iter().map(Self::wrap).collect()
    }

    /// Unwraps a Python sequence of expressions.
    ///
    /// # Errors
    ///
    /// Propagates the per-element extraction error.
    pub(crate) fn vec_from_py(values: &Bound<'_, PyAny>) -> PyResult<Vec<CasExpr>> {
        values
            .try_iter()?
            .map(|item| Ok(item?.extract::<Expr>()?.inner))
            .collect()
    }
}

#[cfg_attr(feature = "stub-gen", pyo3_stub_gen::derive::gen_stub_pymethods)]
#[pymethods]
impl Expr {
    /// An exact integer constant.
    #[staticmethod]
    fn int(n: i128) -> Expr {
        Expr::wrap(CasExpr::int(n))
    }

    /// An exact rational constant `num / den`.
    ///
    /// # Errors
    ///
    /// Raises `ValueError` when `den` is zero. The Rust `CasExpr::rat` *panics*
    /// there; this goes through `Rational::checked_new` instead.
    #[staticmethod]
    #[pyo3(signature = (num, den = 1))]
    fn rat(num: i128, den: i128) -> PyResult<Expr> {
        let value = rational::checked(num, den).ok_or_else(|| {
            PyValueError::new_err(format!(
                "Expr.rat({num}, {den}): denominator must be nonzero and the normalized \
                 pair must fit in i128"
            ))
        })?;
        Ok(Expr::wrap(CasExpr::Const(value)))
    }

    /// A named variable.
    #[staticmethod]
    fn var(name: &str) -> Expr {
        Expr::wrap(CasExpr::var(name))
    }

    /// The constant `0`.
    #[staticmethod]
    fn zero() -> Expr {
        Expr::wrap(CasExpr::zero())
    }

    /// The constant `1`.
    #[staticmethod]
    fn one() -> Expr {
        Expr::wrap(CasExpr::one())
    }

    /// The imaginary unit `i`.
    #[staticmethod]
    fn imaginary_unit() -> Expr {
        Expr::wrap(CasExpr::imaginary_unit())
    }

    /// `self ** exp` for a non-negative integer `exp`.
    ///
    /// The exponent is a `u32`: the fragment has no negative or symbolic powers.
    fn pow(&self, exp: u32) -> Expr {
        Expr::wrap(self.inner.clone().pow(exp))
    }

    /// The principal `q`-th root `self ** (1/q)`.
    fn nth_root(&self, q: u32) -> Expr {
        Expr::wrap(self.inner.clone().nth_root(q))
    }

    /// The polygamma function of order `n`.
    fn polygamma(&self, n: u32) -> Expr {
        Expr::wrap(self.inner.clone().polygamma(n))
    }

    /// The Bessel function of the first kind, order `n`.
    fn bessel_j(&self, n: u32) -> Expr {
        Expr::wrap(self.inner.clone().bessel_j(n))
    }

    /// The modified Bessel function of the first kind, order `n`.
    fn bessel_i(&self, n: u32) -> Expr {
        Expr::wrap(self.inner.clone().bessel_i(n))
    }

    /// Natural logarithm.
    ///
    /// The Rust builder consumes `self`, so this clones.
    fn ln(&self) -> Expr {
        Expr::wrap(self.inner.clone().ln())
    }

    /// Exponential.
    ///
    /// The Rust builder consumes `self`, so this clones.
    fn exp(&self) -> Expr {
        Expr::wrap(self.inner.clone().exp())
    }

    /// Sine.
    ///
    /// The Rust builder consumes `self`, so this clones.
    fn sin(&self) -> Expr {
        Expr::wrap(self.inner.clone().sin())
    }

    /// Cosine.
    ///
    /// The Rust builder consumes `self`, so this clones.
    fn cos(&self) -> Expr {
        Expr::wrap(self.inner.clone().cos())
    }

    /// Tangent.
    ///
    /// The Rust builder consumes `self`, so this clones.
    fn tan(&self) -> Expr {
        Expr::wrap(self.inner.clone().tan())
    }

    /// Arctangent.
    ///
    /// The Rust builder consumes `self`, so this clones.
    fn atan(&self) -> Expr {
        Expr::wrap(self.inner.clone().atan())
    }

    /// Principal square root.
    ///
    /// The Rust builder consumes `self`, so this clones.
    fn sqrt(&self) -> Expr {
        Expr::wrap(self.inner.clone().sqrt())
    }

    /// Principal cube root.
    ///
    /// The Rust builder consumes `self`, so this clones.
    fn cbrt(&self) -> Expr {
        Expr::wrap(self.inner.clone().cbrt())
    }

    /// The Airy function `Ai`.
    ///
    /// The Rust builder consumes `self`, so this clones.
    fn airy_ai(&self) -> Expr {
        Expr::wrap(self.inner.clone().airy_ai())
    }

    /// The Airy function `Bi`.
    ///
    /// The Rust builder consumes `self`, so this clones.
    fn airy_bi(&self) -> Expr {
        Expr::wrap(self.inner.clone().airy_bi())
    }

    /// The principal branch of the Lambert `W` function.
    ///
    /// The Rust builder consumes `self`, so this clones.
    fn lambert_w(&self) -> Expr {
        Expr::wrap(self.inner.clone().lambert_w())
    }

    /// The error function.
    ///
    /// The Rust builder consumes `self`, so this clones.
    fn erf(&self) -> Expr {
        Expr::wrap(self.inner.clone().erf())
    }

    /// The gamma function.
    ///
    /// The Rust builder consumes `self`, so this clones.
    fn gamma(&self) -> Expr {
        Expr::wrap(self.inner.clone().gamma())
    }

    /// The digamma function.
    ///
    /// The Rust builder consumes `self`, so this clones.
    fn digamma(&self) -> Expr {
        Expr::wrap(self.inner.clone().digamma())
    }

    /// The factorial, as `Gamma(x + 1)`.
    ///
    /// The Rust builder consumes `self`, so this clones.
    fn factorial(&self) -> Expr {
        Expr::wrap(self.inner.clone().factorial())
    }

    /// The sine integral `Si`.
    ///
    /// The Rust builder consumes `self`, so this clones.
    fn si(&self) -> Expr {
        Expr::wrap(self.inner.clone().si())
    }

    /// The cosine integral `Ci`.
    ///
    /// The Rust builder consumes `self`, so this clones.
    fn ci(&self) -> Expr {
        Expr::wrap(self.inner.clone().ci())
    }

    /// The exponential integral `Ei`.
    ///
    /// The Rust builder consumes `self`, so this clones.
    fn ei(&self) -> Expr {
        Expr::wrap(self.inner.clone().ei())
    }

    /// The logarithmic integral `li`.
    ///
    /// The Rust builder consumes `self`, so this clones.
    fn li(&self) -> Expr {
        Expr::wrap(self.inner.clone().li())
    }

    /// Absolute value.
    ///
    /// The Rust builder consumes `self`, so this clones.
    fn abs(&self) -> Expr {
        Expr::wrap(self.inner.clone().abs())
    }

    /// The sign function.
    ///
    /// The Rust builder consumes `self`, so this clones.
    fn sign(&self) -> Expr {
        Expr::wrap(self.inner.clone().sign())
    }

    /// The floor function.
    ///
    /// The Rust builder consumes `self`, so this clones.
    fn floor(&self) -> Expr {
        Expr::wrap(self.inner.clone().floor())
    }

    /// The ceiling function.
    ///
    /// The Rust builder consumes `self`, so this clones.
    fn ceiling(&self) -> Expr {
        Expr::wrap(self.inner.clone().ceiling())
    }

    /// The exact derivative with respect to `var`. Total: always succeeds.
    fn differentiate(&self, var: &str) -> Expr {
        Expr::wrap(self.inner.differentiate(var))
    }

    /// The `n`-th derivative with respect to `var`.
    fn differentiate_n(&self, var: &str, n: usize) -> Expr {
        Expr::wrap(self.inner.differentiate_n(var, n))
    }

    /// `self` with every occurrence of `var` replaced by `replacement`.
    fn substitute(&self, var: &str, replacement: &Expr) -> Expr {
        Expr::wrap(self.inner.substitute(var, &replacement.inner))
    }

    /// Exact evaluation under `env`, or `None`.
    ///
    /// `None` means an unbound variable or an `i128` overflow — an honest
    /// undecided, never an error.
    ///
    /// # Errors
    ///
    /// Raises `ValueError` when a binding is not a rational.
    fn eval<'py>(
        &self,
        py: Python<'py>,
        env: &Bound<'py, PyDict>,
    ) -> PyResult<Option<PyFraction<'py>>> {
        let bindings = rational_env(env)?;
        rational::optional_fraction(py, self.inner.eval(&bindings))
    }

    /// The set of variables this expression mentions, sorted.
    fn variables(&self) -> Vec<String> {
        let mut found = std::collections::BTreeSet::new();
        collect_variables(&self.inner, &mut found);
        found.into_iter().collect()
    }

    fn __add__(&self, other: Operand) -> Expr {
        Expr::wrap(self.inner.clone() + other.0)
    }

    fn __radd__(&self, other: Operand) -> Expr {
        Expr::wrap(other.0 + self.inner.clone())
    }

    fn __sub__(&self, other: Operand) -> Expr {
        Expr::wrap(self.inner.clone() - other.0)
    }

    fn __rsub__(&self, other: Operand) -> Expr {
        Expr::wrap(other.0 - self.inner.clone())
    }

    fn __mul__(&self, other: Operand) -> Expr {
        Expr::wrap(self.inner.clone() * other.0)
    }

    fn __rmul__(&self, other: Operand) -> Expr {
        Expr::wrap(other.0 * self.inner.clone())
    }

    fn __truediv__(&self, other: Operand) -> Expr {
        Expr::wrap(self.inner.clone() / other.0)
    }

    fn __rtruediv__(&self, other: Operand) -> Expr {
        Expr::wrap(other.0 / self.inner.clone())
    }

    fn __neg__(&self) -> Expr {
        Expr::wrap(-self.inner.clone())
    }

    /// `self ** exp`; the three-argument (modular) form is not defined here.
    ///
    /// # Errors
    ///
    /// Raises `TypeError` when a modulus is supplied.
    // `exponent`, not `exp`: `pyo3-stub-gen` assumes CPython's own
    // `(exponent, modulo=None)` for `__pow__` and matches the Rust parameter
    // names against it, while PyO3 refuses `#[pyo3(signature = ...)]` on a magic
    // method -- so the name is the only place the two can be reconciled. The
    // parameter is positional in every call `**` makes, so nothing observable
    // changes.
    fn __pow__(&self, exponent: u32, modulo: Option<&Bound<'_, PyAny>>) -> PyResult<Expr> {
        if modulo.is_some_and(|value| !value.is_none()) {
            return Err(pyo3::exceptions::PyTypeError::new_err(
                "Expr.__pow__ takes no modulus",
            ));
        }
        Ok(self.pow(exponent))
    }

    fn __eq__(&self, other: &Bound<'_, PyAny>) -> bool {
        // `cast` + `get`, never `extract`: `extract` on a `#[pyclass]` CLONES the
        // whole wrapped value -- an entire expression tree or certificate -- to
        // compare it and then drops it, and builds a `TypeError` object for the
        // ordinary `NotImplemented` case. `frozen` makes `Bound::get` a borrow
        // with no runtime borrow check at all.
        other
            .cast::<Expr>()
            .is_ok_and(|other| other.get().inner == self.inner)
    }

    fn __hash__(&self) -> u64 {
        // `Display` is a deterministic function of the tree, so structurally
        // equal expressions render alike and hash alike. (The converse is not
        // claimed, and Python does not need it.)
        use std::hash::{Hash, Hasher};
        let mut hasher = std::collections::hash_map::DefaultHasher::new();
        self.inner.to_string().hash(&mut hasher);
        hasher.finish()
    }

    /// The rendered expression. **Not** parseable back into an `Expr`.
    fn __str__(&self) -> String {
        self.inner.to_string()
    }

    fn __repr__(&self) -> String {
        format!("Expr({:?})", self.inner.to_string())
    }
}

/// Collects the variables of an expression.
fn collect_variables(expr: &CasExpr, found: &mut std::collections::BTreeSet<String>) {
    match expr {
        CasExpr::Const(_) => {}
        CasExpr::Var(name) => {
            found.insert(name.clone());
        }
        CasExpr::Add(parts) | CasExpr::Mul(parts) => {
            for part in parts {
                collect_variables(part, found);
            }
        }
        CasExpr::Neg(inner) | CasExpr::Pow(inner, _) | CasExpr::Unary(_, inner) => {
            collect_variables(inner, found);
        }
        CasExpr::Div(numerator, denominator) => {
            collect_variables(numerator, found);
            collect_variables(denominator, found);
        }
    }
}

/// Reads a `{name: rational}` dictionary.
///
/// # Errors
///
/// Raises `ValueError` when a value is not a rational.
pub(crate) fn rational_env(env: &Bound<'_, PyDict>) -> PyResult<BTreeMap<String, IrRational>> {
    let mut bindings = BTreeMap::new();
    for (key, value) in env {
        bindings.insert(key.extract::<String>()?, rational::from_py(&value)?);
    }
    Ok(bindings)
}

/// Reads a `{name: float}` dictionary into the owned pairs `evalf` wants.
///
/// # Errors
///
/// Propagates the per-entry extraction error.
pub(crate) fn float_env(env: &Bound<'_, PyDict>) -> PyResult<Vec<(String, f64)>> {
    let mut bindings = Vec::new();
    for (key, value) in env {
        bindings.push((key.extract::<String>()?, value.extract::<f64>()?));
    }
    Ok(bindings)
}

/// The result of a decidable zero test — the CAS's smallest certificate.
///
/// `Certified` carries the *witness*: the difference `a - b` in canonical form.
/// Re-normalizing that difference is the independent re-check, which is why the
/// witness is exposed rather than folded into a bool. `Unknown` is an `i128`
/// overflow — an honest undecided, never a wrong answer.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyclass(module = "axeyum._native.cas")
)]
#[pyclass(frozen, from_py_object, module = "axeyum", name = "ZeroTest")]
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ZeroTest {
    inner: CasZeroTest,
}

impl ZeroTest {
    /// Wraps a Rust zero test.
    pub(crate) fn wrap(inner: CasZeroTest) -> Self {
        Self { inner }
    }
}

#[cfg_attr(feature = "stub-gen", pyo3_stub_gen::derive::gen_stub_pymethods)]
#[pymethods]
impl ZeroTest {
    /// `"certified"` or `"unknown"` — the variant tag.
    #[getter]
    fn kind(&self) -> &'static str {
        match self.inner {
            CasZeroTest::Certified { .. } => "certified",
            CasZeroTest::Unknown => "unknown",
        }
    }

    /// Whether the test decided at all (as opposed to overflowing).
    fn is_decided(&self) -> bool {
        matches!(self.inner, CasZeroTest::Certified { .. })
    }

    /// Whether the two expressions were decided **equal**.
    ///
    /// `None` on `Unknown`: an undecided test is not a `False`.
    #[getter]
    fn equal(&self) -> Option<bool> {
        match self.inner {
            CasZeroTest::Certified { equal, .. } => Some(equal),
            CasZeroTest::Unknown => None,
        }
    }

    /// The witness: the difference `a - b` in canonical form.
    ///
    /// `None` on `Unknown`. This is the certificate — re-normalize the
    /// difference yourself and confirm it agrees.
    #[getter]
    fn witness(&self) -> Option<MultiPoly> {
        match &self.inner {
            CasZeroTest::Certified { witness, .. } => Some(MultiPoly::wrap(witness.clone())),
            CasZeroTest::Unknown => None,
        }
    }

    /// The trust tag for this answer.
    fn certainty(&self) -> Certainty {
        Certainty::wrap(self.inner.certainty())
    }

    fn __eq__(&self, other: &Bound<'_, PyAny>) -> bool {
        // `cast` + `get`, never `extract`: `extract` on a `#[pyclass]` CLONES the
        // whole wrapped value -- an entire expression tree or certificate -- to
        // compare it and then drops it, and builds a `TypeError` object for the
        // ordinary `NotImplemented` case. `frozen` makes `Bound::get` a borrow
        // with no runtime borrow check at all.
        other
            .cast::<ZeroTest>()
            .is_ok_and(|other| other.get().inner == self.inner)
    }

    fn __repr__(&self) -> String {
        match &self.inner {
            CasZeroTest::Certified { equal, witness } => {
                format!("ZeroTest(Certified, equal={equal}, witness={witness:?})")
            }
            CasZeroTest::Unknown => "ZeroTest(Unknown)".to_owned(),
        }
    }
}

/// An antiderivative that carries its own proof.
///
/// The `certificate` is `equal(d(antiderivative)/dvar, integrand)` — a
/// first-class [`ZeroTest`], not a bool, so a caller can inspect the witness
/// rather than trust the flag.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyclass(module = "axeyum._native.cas")
)]
#[pyclass(frozen, from_py_object, module = "axeyum", name = "CertifiedIntegral")]
#[derive(Debug, Clone)]
pub struct CertifiedIntegral {
    inner: CasCertifiedIntegral,
}

impl CertifiedIntegral {
    /// Wraps a Rust certified integral.
    pub(crate) fn wrap(inner: CasCertifiedIntegral) -> Self {
        Self { inner }
    }
}

#[cfg_attr(feature = "stub-gen", pyo3_stub_gen::derive::gen_stub_pymethods)]
#[pymethods]
impl CertifiedIntegral {
    /// The computed antiderivative `F` (up to `+ C`).
    #[getter]
    fn antiderivative(&self) -> Expr {
        Expr::wrap(self.inner.antiderivative.clone())
    }

    /// The differentiate-and-check certificate.
    #[getter]
    fn certificate(&self) -> ZeroTest {
        ZeroTest::wrap(self.inner.certificate.clone())
    }

    /// Whether the certificate decided the obligation as an exact equality.
    fn is_certified(&self) -> bool {
        self.inner.is_certified()
    }

    fn __repr__(&self) -> String {
        format!(
            "CertifiedIntegral(antiderivative={:?}, certified={})",
            self.inner.antiderivative.to_string(),
            self.inner.is_certified()
        )
    }
}

/// A definite integral, with the antiderivative and certificate it came from.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyclass(module = "axeyum._native.cas")
)]
#[pyclass(frozen, from_py_object, module = "axeyum", name = "DefiniteIntegral")]
#[derive(Debug, Clone)]
pub struct DefiniteIntegral {
    inner: CasDefiniteIntegral,
}

impl DefiniteIntegral {
    /// Wraps a Rust definite integral.
    pub(crate) fn wrap(inner: CasDefiniteIntegral) -> Self {
        Self { inner }
    }
}

#[cfg_attr(feature = "stub-gen", pyo3_stub_gen::derive::gen_stub_pymethods)]
#[pymethods]
impl DefiniteIntegral {
    /// The evaluated value `F(b) - F(a)`.
    #[getter]
    fn value(&self) -> Expr {
        Expr::wrap(self.inner.value.clone())
    }

    /// The antiderivative used.
    #[getter]
    fn antiderivative(&self) -> Expr {
        Expr::wrap(self.inner.antiderivative.clone())
    }

    /// The certificate carried over from the indefinite integral.
    #[getter]
    fn certificate(&self) -> ZeroTest {
        ZeroTest::wrap(self.inner.certificate.clone())
    }

    /// Whether the underlying antiderivative was certified.
    fn is_certified(&self) -> bool {
        self.inner.is_certified()
    }

    fn __repr__(&self) -> String {
        format!(
            "DefiniteIntegral(value={:?}, certified={})",
            self.inner.value.to_string(),
            self.inner.is_certified()
        )
    }
}

/// The point a limit is taken at.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyclass(module = "axeyum._native.cas")
)]
#[pyclass(frozen, from_py_object, module = "axeyum", name = "LimitPoint")]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct LimitPoint {
    inner: CasLimitPoint,
}

impl LimitPoint {
    /// The wrapped Rust limit point.
    pub(crate) fn inner(self) -> CasLimitPoint {
        self.inner
    }
}

#[cfg_attr(feature = "stub-gen", pyo3_stub_gen::derive::gen_stub_pymethods)]
#[pymethods]
impl LimitPoint {
    /// A finite rational point.
    ///
    /// # Errors
    ///
    /// Raises `ValueError` when `value` is not an exact rational.
    #[staticmethod]
    fn finite(value: RationalLike<'_>) -> PyResult<LimitPoint> {
        Ok(LimitPoint {
            inner: CasLimitPoint::Finite(rational::from_py(value.as_any())?),
        })
    }

    /// `x -> +infinity`.
    #[staticmethod]
    fn pos_infinity() -> LimitPoint {
        LimitPoint {
            inner: CasLimitPoint::PosInfinity,
        }
    }

    /// `x -> -infinity`.
    #[staticmethod]
    fn neg_infinity() -> LimitPoint {
        LimitPoint {
            inner: CasLimitPoint::NegInfinity,
        }
    }

    fn __repr__(&self) -> String {
        match self.inner {
            CasLimitPoint::Finite(value) => format!(
                "LimitPoint.finite({}/{})",
                value.numerator(),
                value.denominator()
            ),
            CasLimitPoint::PosInfinity => "LimitPoint.pos_infinity()".to_owned(),
            CasLimitPoint::NegInfinity => "LimitPoint.neg_infinity()".to_owned(),
        }
    }
}

/// A set of sign assumptions about named variables.
///
/// Every builder returns a **new** context, mirroring the Rust consuming
/// builder; nothing here mutates in place.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyclass(module = "axeyum._native.cas")
)]
#[pyclass(frozen, from_py_object, module = "axeyum", name = "Assumptions")]
#[derive(Debug, Clone, Default)]
pub struct Assumptions {
    inner: CasAssumptions,
}

impl Assumptions {
    /// The wrapped assumption context.
    pub(crate) fn inner(&self) -> &CasAssumptions {
        &self.inner
    }
}

#[cfg_attr(feature = "stub-gen", pyo3_stub_gen::derive::gen_stub_pymethods)]
#[pymethods]
impl Assumptions {
    /// An empty assumption context.
    #[new]
    fn new() -> Assumptions {
        Assumptions {
            inner: CasAssumptions::new(),
        }
    }

    /// This context plus `var > 0`.
    fn positive(&self, var: &str) -> Assumptions {
        Assumptions {
            inner: self.inner.clone().positive(var),
        }
    }

    /// This context plus `var < 0`.
    fn negative(&self, var: &str) -> Assumptions {
        Assumptions {
            inner: self.inner.clone().negative(var),
        }
    }

    /// This context plus `var >= 0`.
    fn nonnegative(&self, var: &str) -> Assumptions {
        Assumptions {
            inner: self.inner.clone().nonnegative(var),
        }
    }

    /// This context plus `var != 0`.
    fn nonzero(&self, var: &str) -> Assumptions {
        Assumptions {
            inner: self.inner.clone().nonzero(var),
        }
    }

    /// The sign this context establishes for `expr`.
    fn sign_of(&self, expr: &Expr) -> Sign {
        Sign::wrap(self.inner.sign_of(expr.inner()))
    }

    /// Whether this context establishes `expr > 0`.
    fn is_positive(&self, expr: &Expr) -> bool {
        self.inner.is_positive(expr.inner())
    }

    /// Whether this context establishes `expr >= 0`.
    fn is_nonnegative(&self, expr: &Expr) -> bool {
        self.inner.is_nonnegative(expr.inner())
    }

    /// Whether this context establishes `expr != 0`.
    fn is_nonzero(&self, expr: &Expr) -> bool {
        self.inner.is_nonzero(expr.inner())
    }

    fn __repr__(&self) -> String {
        "Assumptions(...)".to_owned()
    }
}
