//! The pure-function surface of `axeyum.cas`.
//!
//! Almost every entry here is `fn(&CasExpr, ...) -> Option<CasExpr>` in Rust, and
//! the `None` is an honest *declined, outside the fragment, or `i128` overflow*.
//! It crosses the boundary as Python `None` — never as an exception, and never
//! coerced into a default (inventory §0.5).

use axeyum_cas::{
    CasExpr, InequalityOp as CasInequalityOp, Matrix as CasMatrix, RealInterval as CasRealInterval,
};
use axeyum_ir::Rational as IrRational;
use pyo3::exceptions::PyValueError;
use pyo3::prelude::*;
use pyo3::types::{PyAny, PyDict, PyModule};

use crate::cas::expr::{
    Assumptions, CertifiedIntegral, DefiniteIntegral, Expr, LimitPoint, ZeroTest, float_env,
};
use crate::cas::poly::MultiPoly;
use crate::cas::rational;

/// Binds `fn(&CasExpr) -> CasExpr`.
macro_rules! total_unary {
    ($name:ident, $doc:literal) => {
        #[doc = $doc]
        #[pyfunction]
        fn $name(expr: &Expr) -> Expr {
            Expr::wrap(axeyum_cas::$name(expr.inner()))
        }
    };
}

/// Binds `fn(&CasExpr) -> Option<CasExpr>`.
macro_rules! partial_unary {
    ($name:ident, $doc:literal) => {
        #[doc = $doc]
        #[pyfunction]
        fn $name(expr: &Expr) -> Option<Expr> {
            Expr::wrap_option(axeyum_cas::$name(expr.inner()))
        }
    };
}

/// Binds `fn(&CasExpr, &str) -> Option<CasExpr>`.
macro_rules! partial_in_var {
    ($name:ident, $doc:literal) => {
        #[doc = $doc]
        #[pyfunction]
        fn $name(expr: &Expr, var: &str) -> Option<Expr> {
            Expr::wrap_option(axeyum_cas::$name(expr.inner(), var))
        }
    };
}

/// Binds `fn(&CasExpr, &CasExpr, &str) -> Option<CasExpr>`.
macro_rules! partial_binary_in_var {
    ($name:ident, $doc:literal) => {
        #[doc = $doc]
        #[pyfunction]
        fn $name(a: &Expr, b: &Expr, var: &str) -> Option<Expr> {
            Expr::wrap_option(axeyum_cas::$name(a.inner(), b.inner(), var))
        }
    };
}

total_unary!(
    simplify,
    "Heuristic simplification. Never returns a wrong form."
);
total_unary!(trigsimp, "Trigonometric simplification.");
total_unary!(simplify_radicals, "Pulls perfect powers out of radicals.");
total_unary!(evaluate_trig, "Evaluates trig at exact special angles.");
total_unary!(
    rewrite_exp,
    "Rewrites hyperbolic/trig heads as exponentials."
);
total_unary!(expand_log, "Expands `ln` of products and powers.");
total_unary!(expand_trig, "Expands trig of sums and multiples.");
total_unary!(logcombine, "Combines a sum of logarithms into one.");
total_unary!(conjugate, "The complex conjugate.");

partial_unary!(expand, "Expands to a flat sum of monomials.");
partial_unary!(cancel, "Cancels common factors in a quotient.");
partial_unary!(real_part, "The real part.");
partial_unary!(imaginary_part, "The imaginary part.");
partial_unary!(modulus, "The complex modulus.");
partial_unary!(argument, "The complex argument.");

partial_in_var!(collect, "Collects terms by powers of `var`.");
partial_in_var!(apart, "Partial-fraction decomposition in `var`.");
partial_in_var!(factor, "Factors a univariate polynomial in `var`.");
partial_in_var!(factor_expr, "Factors over the rationals, certified.");
partial_in_var!(leading_coeff, "The leading coefficient in `var`.");
partial_in_var!(content, "The content (gcd of coefficients) in `var`.");
partial_in_var!(primitive_part, "The primitive part in `var`.");
partial_in_var!(discriminant, "The discriminant in `var`.");
partial_in_var!(
    sum_polynomial,
    "The indefinite sum of a polynomial in `var`."
);
partial_in_var!(gosper_sum, "Gosper's indefinite hypergeometric summation.");

partial_binary_in_var!(poly_gcd, "Polynomial gcd in `var`.");
partial_binary_in_var!(poly_lcm, "Polynomial lcm in `var`.");
partial_binary_in_var!(resultant, "The resultant in `var`.");

/// The canonical polynomial normal form of `expr`, or `None` when it is outside
/// the polynomial fragment (or overflows).
#[pyfunction]
fn normalize(expr: &Expr) -> Option<MultiPoly> {
    MultiPoly::wrap_option(axeyum_cas::normalize(expr.inner()))
}

/// The decidable zero test `a == b`, with a re-checkable witness.
///
/// The returned [`ZeroTest`] is the certificate, not a bool: `Certified` carries
/// the canonical form of `a - b`, which an independent caller can re-normalize.
#[pyfunction]
fn equal(a: &Expr, b: &Expr) -> ZeroTest {
    ZeroTest::wrap(axeyum_cas::equal(a.inner(), b.inner()))
}

/// Checks a claimed derivative directly, returning the certificate.
#[pyfunction]
fn prove_derivative(expr: &Expr, var: &str, claimed: &Expr) -> ZeroTest {
    ZeroTest::wrap(axeyum_cas::prove_derivative(
        expr.inner(),
        var,
        claimed.inner(),
    ))
}

/// Simplification under sign assumptions.
#[pyfunction]
fn simplify_under_assumptions(expr: &Expr, assumptions: &Assumptions) -> Expr {
    Expr::wrap(axeyum_cas::simplify_under_assumptions(
        expr.inner(),
        assumptions.inner(),
    ))
}

/// The degree of `expr` in `var`, or `None` when it is not a polynomial there.
#[pyfunction]
fn degree(expr: &Expr, var: &str) -> Option<usize> {
    axeyum_cas::degree(expr.inner(), var)
}

/// The coefficient of `var ** n`.
#[pyfunction]
fn coeff(expr: &Expr, var: &str, n: usize) -> Option<Expr> {
    Expr::wrap_option(axeyum_cas::coeff(expr.inner(), var, n))
}

/// Whether `expr` is irreducible over the rationals in `var`; `None` when
/// undecided.
#[pyfunction]
fn is_irreducible(expr: &Expr, var: &str) -> Option<bool> {
    axeyum_cas::is_irreducible(expr.inner(), var)
}

/// `(quotient, remainder)` of polynomial division in `var`.
#[pyfunction]
fn poly_div(a: &Expr, b: &Expr, var: &str) -> Option<(Expr, Expr)> {
    axeyum_cas::poly_div(a.inner(), b.inner(), var)
        .map(|(quotient, remainder)| (Expr::wrap(quotient), Expr::wrap(remainder)))
}

/// The exact roots of `expr` in `var`, or `None`.
#[pyfunction]
fn solve(expr: &Expr, var: &str) -> Option<Vec<Expr>> {
    axeyum_cas::solve(expr.inner(), var).map(Expr::wrap_vec)
}

/// Solves a linear system, returning `[(variable, value), ...]`.
///
/// # Errors
///
/// Propagates the per-element extraction error.
#[pyfunction]
fn solve_linear_system(
    equations: &Bound<'_, PyAny>,
    vars: Vec<String>,
) -> PyResult<Option<Vec<(String, Expr)>>> {
    let equations = Expr::vec_from_py(equations)?;
    let borrowed: Vec<&str> = vars.iter().map(String::as_str).collect();
    Ok(
        axeyum_cas::solve_linear_system(&equations, &borrowed).map(|solution| {
            solution
                .into_iter()
                .map(|(name, value)| (name, Expr::wrap(value)))
                .collect()
        }),
    )
}

/// Solves a bivariate polynomial system, returning `[(x, y), ...]`.
#[pyfunction]
fn solve_polynomial_system(
    f: &Expr,
    g: &Expr,
    xvar: &str,
    yvar: &str,
) -> Option<Vec<(Expr, Expr)>> {
    axeyum_cas::solve_polynomial_system(f.inner(), g.inner(), xvar, yvar).map(|solutions| {
        solutions
            .into_iter()
            .map(|(x, y)| (Expr::wrap(x), Expr::wrap(y)))
            .collect()
    })
}

/// A real interval with rational or infinite endpoints.
#[pyclass(frozen, from_py_object, module = "axeyum", name = "RealInterval")]
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RealInterval {
    inner: CasRealInterval,
}

#[pymethods]
impl RealInterval {
    /// The lower endpoint, or `None` for `-infinity`.
    ///
    /// # Errors
    ///
    /// Propagates any Python error raised while building the fraction.
    #[getter]
    fn lower<'py>(&self, py: Python<'py>) -> PyResult<Option<Bound<'py, PyAny>>> {
        rational::optional_fraction(py, self.inner.lower)
    }

    /// Whether the lower endpoint is included.
    #[getter]
    fn lower_closed(&self) -> bool {
        self.inner.lower_closed
    }

    /// The upper endpoint, or `None` for `+infinity`.
    ///
    /// # Errors
    ///
    /// Propagates any Python error raised while building the fraction.
    #[getter]
    fn upper<'py>(&self, py: Python<'py>) -> PyResult<Option<Bound<'py, PyAny>>> {
        rational::optional_fraction(py, self.inner.upper)
    }

    /// Whether the upper endpoint is included.
    #[getter]
    fn upper_closed(&self) -> bool {
        self.inner.upper_closed
    }

    fn __repr__(&self) -> String {
        let render = |value: Option<IrRational>, fallback: &str| {
            value.map_or_else(
                || fallback.to_owned(),
                |value| format!("{}/{}", value.numerator(), value.denominator()),
            )
        };
        format!(
            "RealInterval({}{}, {}{})",
            if self.inner.lower_closed { "[" } else { "(" },
            render(self.inner.lower, "-inf"),
            render(self.inner.upper, "inf"),
            if self.inner.upper_closed { "]" } else { ")" },
        )
    }
}

/// Solves `p(var) OP 0` over the reals as a union of disjoint intervals.
///
/// `op` is one of `">"`, `">="`, `"<"`, `"<="`.
///
/// # Errors
///
/// Raises `ValueError` for an unrecognized `op`.
#[pyfunction]
fn solve_polynomial_inequality(
    expr: &Expr,
    var: &str,
    op: &str,
) -> PyResult<Option<Vec<RealInterval>>> {
    let op = match op {
        ">" => CasInequalityOp::Greater,
        ">=" => CasInequalityOp::GreaterEqual,
        "<" => CasInequalityOp::Less,
        "<=" => CasInequalityOp::LessEqual,
        other => {
            return Err(PyValueError::new_err(format!(
                "unknown inequality operator {other:?}; expected one of >, >=, <, <="
            )));
        }
    };
    Ok(
        axeyum_cas::solve_polynomial_inequality(expr.inner(), var, op).map(|intervals| {
            intervals
                .into_iter()
                .map(|inner| RealInterval { inner })
                .collect()
        }),
    )
}

/// Sturm-isolating intervals, one per distinct real root, ascending.
///
/// # Errors
///
/// Propagates any Python error raised while building the fractions.
#[pyfunction]
fn real_root_intervals<'py>(
    py: Python<'py>,
    expr: &Expr,
    var: &str,
) -> PyResult<Option<Vec<(Bound<'py, PyAny>, Bound<'py, PyAny>)>>> {
    axeyum_cas::real_root_intervals(expr.inner(), var)
        .map(|intervals| {
            intervals
                .into_iter()
                .map(|(lower, upper)| {
                    Ok((
                        rational::fraction(py, lower)?,
                        rational::fraction(py, upper)?,
                    ))
                })
                .collect::<PyResult<Vec<_>>>()
        })
        .transpose()
}

/// The exact number of distinct real roots in `[lower, upper]`.
///
/// # Errors
///
/// Raises `ValueError` when an endpoint is not an exact rational.
#[pyfunction]
fn count_real_roots(
    expr: &Expr,
    var: &str,
    lower: &Bound<'_, PyAny>,
    upper: &Bound<'_, PyAny>,
) -> PyResult<Option<usize>> {
    Ok(axeyum_cas::count_real_roots(
        expr.inner(),
        var,
        rational::from_py(lower)?,
        rational::from_py(upper)?,
    ))
}

/// Rational approximations of every real root, to within `width`.
///
/// # Errors
///
/// Raises `ValueError` when `width` is not an exact rational.
#[pyfunction]
fn approximate_real_roots<'py>(
    py: Python<'py>,
    expr: &Expr,
    var: &str,
    width: &Bound<'py, PyAny>,
) -> PyResult<Option<Vec<Bound<'py, PyAny>>>> {
    let width = rational::from_py(width)?;
    axeyum_cas::approximate_real_roots(expr.inner(), var, width)
        .map(|roots| {
            roots
                .into_iter()
                .map(|root| rational::fraction(py, root))
                .collect::<PyResult<Vec<_>>>()
        })
        .transpose()
}

/// The limit of `expr` as `var` approaches `point`.
#[pyfunction]
fn limit(expr: &Expr, var: &str, point: &LimitPoint) -> Option<Expr> {
    Expr::wrap_option(axeyum_cas::limit(expr.inner(), var, point.inner()))
}

/// The Maclaurin series of `expr` to `order`.
#[pyfunction]
fn series(expr: &Expr, var: &str, order: usize) -> Option<Expr> {
    Expr::wrap_option(axeyum_cas::series(expr.inner(), var, order))
}

/// The Taylor series of `expr` about `center` to `order`.
#[pyfunction]
fn series_at(expr: &Expr, var: &str, center: &Expr, order: usize) -> Option<Expr> {
    Expr::wrap_option(axeyum_cas::series_at(
        expr.inner(),
        var,
        center.inner(),
        order,
    ))
}

/// An antiderivative that carries its own proof, or `None` when declined.
///
/// The result's `certificate` is a [`ZeroTest`] over
/// `d(antiderivative)/dvar - integrand`.
#[pyfunction]
fn integrate(expr: &Expr, var: &str) -> Option<CertifiedIntegral> {
    axeyum_cas::integrate(expr.inner(), var).map(CertifiedIntegral::wrap)
}

/// A definite integral, with the antiderivative and certificate it came from.
#[pyfunction]
fn definite_integrate(
    expr: &Expr,
    var: &str,
    lower: &Expr,
    upper: &Expr,
) -> Option<DefiniteIntegral> {
    axeyum_cas::definite_integrate(expr.inner(), var, lower.inner(), upper.inner())
        .map(DefiniteIntegral::wrap)
}

/// Floating-point evaluation under `bindings`, or `None`.
///
/// # Errors
///
/// Propagates the per-entry extraction error.
#[pyfunction]
fn evalf(expr: &Expr, bindings: &Bound<'_, PyDict>) -> PyResult<Option<f64>> {
    let owned = float_env(bindings)?;
    let borrowed: Vec<(&str, f64)> = owned
        .iter()
        .map(|(name, value)| (name.as_str(), *value))
        .collect();
    Ok(axeyum_cas::evalf(expr.inner(), &borrowed))
}

/// The best rational approximation of `x` with denominator at most
/// `max_denominator`.
///
/// # Errors
///
/// Propagates any Python error raised while building the fraction.
#[pyfunction]
fn rationalize(
    py: Python<'_>,
    x: f64,
    max_denominator: i128,
) -> PyResult<Option<Bound<'_, PyAny>>> {
    rational::optional_fraction(py, axeyum_cas::rationalize(x, max_denominator))
}

/// A symbolic value matching the float `value`, or `None`.
#[pyfunction]
fn nsimplify(value: f64, max_denominator: i128) -> Option<Expr> {
    Expr::wrap_option(axeyum_cas::nsimplify(value, max_denominator))
}

/// The residue of `expr` at the rational `point`.
///
/// # Errors
///
/// Raises `ValueError` when `point` is not an exact rational.
#[pyfunction]
fn residue(expr: &Expr, var: &str, point: &Bound<'_, PyAny>) -> PyResult<Option<Expr>> {
    Ok(Expr::wrap_option(axeyum_cas::residue(
        expr.inner(),
        var,
        rational::from_py(point)?,
    )))
}

/// The definite sum of `f` over `var` from `lower` to `upper`.
#[pyfunction]
fn definite_sum(f: &Expr, var: &str, lower: &Expr, upper: &Expr) -> Option<Expr> {
    Expr::wrap_option(axeyum_cas::definite_sum(
        f.inner(),
        var,
        lower.inner(),
        upper.inner(),
    ))
}

/// The infinite sum of `f` over `var` from `lower`.
#[pyfunction]
fn infinite_sum(f: &Expr, var: &str, lower: &Expr) -> Option<Expr> {
    Expr::wrap_option(axeyum_cas::infinite_sum(f.inner(), var, lower.inner()))
}

/// The finite product of `f` over `var` from `lower` to `upper`.
#[pyfunction]
fn finite_product(f: &Expr, var: &str, lower: &Expr, upper: &Expr) -> Option<Expr> {
    Expr::wrap_option(axeyum_cas::finite_product(
        f.inner(),
        var,
        lower.inner(),
        upper.inner(),
    ))
}

/// Solves the Euler-Cauchy equation with the given coefficients.
///
/// # Errors
///
/// Raises `ValueError` when a coefficient is not an exact rational.
#[pyfunction]
fn dsolve_euler_cauchy(coeffs: &Bound<'_, PyAny>, var: &str) -> PyResult<Option<Expr>> {
    let coeffs = rational::vec_from_py(coeffs)?;
    Ok(Expr::wrap_option(axeyum_cas::dsolve_euler_cauchy(
        &coeffs, var,
    )))
}

/// Solves a constant-coefficient homogeneous linear ODE.
///
/// # Errors
///
/// Raises `ValueError` when a coefficient is not an exact rational.
#[pyfunction]
fn dsolve_homogeneous(char_coeffs: &Bound<'_, PyAny>, var: &str) -> PyResult<Option<Expr>> {
    let coeffs = rational::vec_from_py(char_coeffs)?;
    Ok(Expr::wrap_option(axeyum_cas::dsolve_homogeneous(
        &coeffs, var,
    )))
}

/// Solves a constant-coefficient inhomogeneous linear ODE.
///
/// # Errors
///
/// Raises `ValueError` when a coefficient is not an exact rational.
#[pyfunction]
fn dsolve_inhomogeneous(
    char_coeffs: &Bound<'_, PyAny>,
    forcing: &Expr,
    var: &str,
) -> PyResult<Option<Expr>> {
    let coeffs = rational::vec_from_py(char_coeffs)?;
    Ok(Expr::wrap_option(axeyum_cas::dsolve_inhomogeneous(
        &coeffs,
        forcing.inner(),
        var,
    )))
}

/// Solves `y' + p(var) y = q(var)`.
#[pyfunction]
fn dsolve_first_order_linear(p: &Expr, q: &Expr, var: &str) -> Option<Expr> {
    Expr::wrap_option(axeyum_cas::dsolve_first_order_linear(
        p.inner(),
        q.inner(),
        var,
    ))
}

/// Solves a separable first-order ODE.
#[pyfunction]
fn dsolve_separable(f: &Expr, g: &Expr, xvar: &str, yvar: &str) -> Option<Expr> {
    Expr::wrap_option(axeyum_cas::dsolve_separable(
        f.inner(),
        g.inner(),
        xvar,
        yvar,
    ))
}

/// Solves an exact first-order ODE.
#[pyfunction]
fn dsolve_exact(m: &Expr, n: &Expr, xvar: &str, yvar: &str) -> Option<Expr> {
    Expr::wrap_option(axeyum_cas::dsolve_exact(m.inner(), n.inner(), xvar, yvar))
}

/// Solves a Bernoulli first-order ODE.
#[pyfunction]
fn dsolve_bernoulli(p: &Expr, q: &Expr, var: &str) -> Option<Expr> {
    Expr::wrap_option(axeyum_cas::dsolve_bernoulli(p.inner(), q.inner(), var))
}

/// Pins the free constants of a general solution to initial conditions given as
/// `[(derivative_order, point, value), ...]`.
///
/// # Errors
///
/// Propagates the per-element extraction error.
#[pyfunction]
fn apply_initial_conditions(
    general: &Expr,
    var: &str,
    conditions: Vec<(usize, Expr, Expr)>,
) -> Option<Expr> {
    let owned: Vec<(usize, CasExpr, CasExpr)> = conditions
        .into_iter()
        .map(|(order, point, value)| (order, point.inner().clone(), value.inner().clone()))
        .collect();
    Expr::wrap_option(axeyum_cas::apply_initial_conditions(
        general.inner(),
        var,
        &owned,
    ))
}

/// Solves a constant-coefficient linear recurrence.
///
/// # Errors
///
/// Raises `ValueError` when a coefficient is not an exact rational.
#[pyfunction]
fn solve_recurrence(
    coefficients: &Bound<'_, PyAny>,
    initial: &Bound<'_, PyAny>,
    var: &str,
) -> PyResult<Option<Expr>> {
    let coefficients = rational::vec_from_py(coefficients)?;
    let initial = rational::vec_from_py(initial)?;
    Ok(Expr::wrap_option(axeyum_cas::solve_recurrence(
        &coefficients,
        &initial,
        var,
    )))
}

/// A dense matrix of expressions.
#[pyclass(frozen, from_py_object, module = "axeyum", name = "Matrix")]
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Matrix {
    inner: CasMatrix,
}

impl Matrix {
    /// Wraps a Rust matrix.
    fn wrap(inner: CasMatrix) -> Self {
        Self { inner }
    }

    /// Wraps an optional Rust matrix.
    fn wrap_option(value: Option<CasMatrix>) -> Option<Self> {
        value.map(Self::wrap)
    }
}

#[pymethods]
impl Matrix {
    /// A matrix from a list of rows, or `None` when the rows are ragged.
    ///
    /// # Errors
    ///
    /// Propagates the per-element extraction error.
    #[staticmethod]
    fn from_rows(rows: &Bound<'_, PyAny>) -> PyResult<Option<Matrix>> {
        let mut collected = Vec::new();
        for row in rows.try_iter()? {
            collected.push(Expr::vec_from_py(&row?)?);
        }
        Ok(Matrix::wrap_option(CasMatrix::from_rows(collected)))
    }

    /// The `n x n` identity.
    #[staticmethod]
    fn identity(n: usize) -> Matrix {
        Matrix::wrap(CasMatrix::identity(n))
    }

    /// An all-zero matrix.
    #[staticmethod]
    fn zeros(rows: usize, cols: usize) -> Matrix {
        Matrix::wrap(CasMatrix::zeros(rows, cols))
    }

    /// The number of rows.
    #[getter]
    fn rows(&self) -> usize {
        self.inner.rows()
    }

    /// The number of columns.
    #[getter]
    fn cols(&self) -> usize {
        self.inner.cols()
    }

    /// The entry at `(row, col)`, or `None` when out of range.
    fn get(&self, row: usize, col: usize) -> Option<Expr> {
        self.inner.get(row, col).cloned().map(Expr::wrap)
    }

    /// The transpose.
    fn transpose(&self) -> Matrix {
        Matrix::wrap(self.inner.transpose())
    }

    /// `self + other`, or `None` on a shape mismatch.
    fn add(&self, other: &Matrix) -> Option<Matrix> {
        Matrix::wrap_option(self.inner.add(&other.inner))
    }

    /// `self - other`, or `None` on a shape mismatch.
    fn sub(&self, other: &Matrix) -> Option<Matrix> {
        Matrix::wrap_option(self.inner.sub(&other.inner))
    }

    /// `self @ other`, or `None` on a shape mismatch.
    fn mul(&self, other: &Matrix) -> Option<Matrix> {
        Matrix::wrap_option(self.inner.mul(&other.inner))
    }

    /// `self ** exponent`, or `None`.
    fn pow(&self, exponent: u32) -> Option<Matrix> {
        Matrix::wrap_option(self.inner.pow(exponent))
    }

    /// The determinant, or `None`.
    fn determinant(&self) -> Option<Expr> {
        Expr::wrap_option(self.inner.determinant())
    }

    /// The reduced row echelon form, or `None`.
    fn rref(&self) -> Option<Matrix> {
        Matrix::wrap_option(self.inner.rref())
    }

    /// A basis of the null space, or `None`.
    fn null_space(&self) -> Option<Vec<Matrix>> {
        self.inner
            .null_space()
            .map(|basis| basis.into_iter().map(Matrix::wrap).collect())
    }

    fn __eq__(&self, other: &Bound<'_, PyAny>) -> bool {
        other
            .extract::<Matrix>()
            .is_ok_and(|other| other.inner == self.inner)
    }

    fn __repr__(&self) -> String {
        format!("Matrix({}x{})", self.inner.rows(), self.inner.cols())
    }
}

/// The rank of a matrix, or `None`.
#[pyfunction]
fn matrix_rank(matrix: &Matrix) -> Option<usize> {
    axeyum_cas::matrix_rank(&matrix.inner)
}

/// The trace, or `None` for a non-square matrix.
#[pyfunction]
fn trace(matrix: &Matrix) -> Option<Expr> {
    Expr::wrap_option(axeyum_cas::trace(&matrix.inner))
}

/// The characteristic polynomial in `var`.
#[pyfunction]
fn characteristic_polynomial(matrix: &Matrix, var: &str) -> Option<Expr> {
    Expr::wrap_option(axeyum_cas::characteristic_polynomial(&matrix.inner, var))
}

/// The minimal polynomial in `var`.
#[pyfunction]
fn minimal_polynomial(matrix: &Matrix, var: &str) -> Option<Expr> {
    Expr::wrap_option(axeyum_cas::minimal_polynomial(&matrix.inner, var))
}

/// The companion matrix of a monic polynomial in `var`.
#[pyfunction]
fn companion_matrix(poly: &Expr, var: &str) -> Option<Matrix> {
    Matrix::wrap_option(axeyum_cas::companion_matrix(poly.inner(), var))
}

/// The eigenvalues, or `None`.
#[pyfunction]
fn eigenvalues(matrix: &Matrix, var: &str) -> Option<Vec<Expr>> {
    axeyum_cas::eigenvalues(&matrix.inner, var).map(Expr::wrap_vec)
}

/// `[(eigenvalue, [eigenvector, ...]), ...]`, or `None`.
#[pyfunction]
fn eigenvectors(matrix: &Matrix, var: &str) -> Option<Vec<(Expr, Vec<Matrix>)>> {
    axeyum_cas::eigenvectors(&matrix.inner, var).map(|pairs| {
        pairs
            .into_iter()
            .map(|(value, vectors)| {
                (
                    Expr::wrap(value),
                    vectors.into_iter().map(Matrix::wrap).collect(),
                )
            })
            .collect()
    })
}

/// `(P, D)` with `A = P D P^-1`, or `None` when not diagonalizable.
#[pyfunction]
fn diagonalize(matrix: &Matrix, var: &str) -> Option<(Matrix, Matrix)> {
    axeyum_cas::diagonalize(&matrix.inner, var).map(|(p, d)| (Matrix::wrap(p), Matrix::wrap(d)))
}

/// The gradient of `expr` with respect to `vars`.
#[pyfunction]
fn gradient(expr: &Expr, vars: Vec<String>) -> Vec<Expr> {
    let borrowed: Vec<&str> = vars.iter().map(String::as_str).collect();
    Expr::wrap_vec(axeyum_cas::gradient(expr.inner(), &borrowed))
}

/// The Jacobian of `exprs` with respect to `vars`.
///
/// # Errors
///
/// Propagates the per-element extraction error.
#[pyfunction]
fn jacobian(exprs: &Bound<'_, PyAny>, vars: Vec<String>) -> PyResult<Option<Matrix>> {
    let exprs = Expr::vec_from_py(exprs)?;
    let borrowed: Vec<&str> = vars.iter().map(String::as_str).collect();
    Ok(Matrix::wrap_option(axeyum_cas::jacobian(&exprs, &borrowed)))
}

/// The Hessian of `f` with respect to `vars`.
#[pyfunction]
fn hessian(f: &Expr, vars: Vec<String>) -> Option<Matrix> {
    let borrowed: Vec<&str> = vars.iter().map(String::as_str).collect();
    Matrix::wrap_option(axeyum_cas::hessian(f.inner(), &borrowed))
}

/// The Laplacian of `f` with respect to `vars`.
#[pyfunction]
fn laplacian(f: &Expr, vars: Vec<String>) -> Expr {
    let borrowed: Vec<&str> = vars.iter().map(String::as_str).collect();
    Expr::wrap(axeyum_cas::laplacian(f.inner(), &borrowed))
}

/// The divergence of a vector field.
///
/// # Errors
///
/// Propagates the per-element extraction error.
#[pyfunction]
fn divergence(field: &Bound<'_, PyAny>, vars: Vec<String>) -> PyResult<Option<Expr>> {
    let field = Expr::vec_from_py(field)?;
    let borrowed: Vec<&str> = vars.iter().map(String::as_str).collect();
    Ok(Expr::wrap_option(axeyum_cas::divergence(&field, &borrowed)))
}

/// The Wronskian of `functions` in `var`.
///
/// # Errors
///
/// Propagates the per-element extraction error.
#[pyfunction]
fn wronskian(functions: &Bound<'_, PyAny>, var: &str) -> PyResult<Option<Expr>> {
    let functions = Expr::vec_from_py(functions)?;
    Ok(Expr::wrap_option(axeyum_cas::wronskian(&functions, var)))
}

/// The `n`-th cyclotomic polynomial in `var`.
#[pyfunction]
fn cyclotomic_polynomial(n: u64, var: &str) -> Option<Expr> {
    Expr::wrap_option(axeyum_cas::cyclotomic_polynomial(n, var))
}

/// The population standard deviation of exact rational data.
///
/// # Errors
///
/// Raises `ValueError` when a datum is not an exact rational.
#[pyfunction]
fn standard_deviation(data: &Bound<'_, PyAny>) -> PyResult<Option<Expr>> {
    let data = rational::vec_from_py(data)?;
    Ok(Expr::wrap_option(axeyum_cas::standard_deviation(&data)))
}

/// The sample standard deviation of exact rational data.
///
/// # Errors
///
/// Raises `ValueError` when a datum is not an exact rational.
#[pyfunction]
fn sample_standard_deviation(data: &Bound<'_, PyAny>) -> PyResult<Option<Expr>> {
    let data = rational::vec_from_py(data)?;
    Ok(Expr::wrap_option(axeyum_cas::sample_standard_deviation(
        &data,
    )))
}

/// Registers the pure-function surface on `module`.
///
/// # Errors
///
/// Propagates any Python error raised while setting the module attributes.
#[allow(clippy::too_many_lines)]
pub(crate) fn register(module: &Bound<'_, PyModule>) -> PyResult<()> {
    module.add_class::<Matrix>()?;
    module.add_class::<RealInterval>()?;
    macro_rules! add {
        ($($name:ident),* $(,)?) => {
            $(module.add_function(wrap_pyfunction!($name, module)?)?;)*
        };
    }
    add!(
        simplify,
        trigsimp,
        simplify_radicals,
        evaluate_trig,
        rewrite_exp,
        expand_log,
        expand_trig,
        logcombine,
        conjugate,
        expand,
        cancel,
        real_part,
        imaginary_part,
        modulus,
        argument,
        collect,
        apart,
        factor,
        factor_expr,
        leading_coeff,
        content,
        primitive_part,
        discriminant,
        sum_polynomial,
        gosper_sum,
        poly_gcd,
        poly_lcm,
        resultant,
        normalize,
        equal,
        prove_derivative,
        simplify_under_assumptions,
        degree,
        coeff,
        is_irreducible,
        poly_div,
        solve,
        solve_linear_system,
        solve_polynomial_system,
        solve_polynomial_inequality,
        real_root_intervals,
        count_real_roots,
        approximate_real_roots,
        limit,
        series,
        series_at,
        integrate,
        definite_integrate,
        evalf,
        rationalize,
        nsimplify,
        residue,
        definite_sum,
        infinite_sum,
        finite_product,
        dsolve_euler_cauchy,
        dsolve_homogeneous,
        dsolve_inhomogeneous,
        dsolve_first_order_linear,
        dsolve_separable,
        dsolve_exact,
        dsolve_bernoulli,
        apply_initial_conditions,
        solve_recurrence,
        matrix_rank,
        trace,
        characteristic_polynomial,
        minimal_polynomial,
        companion_matrix,
        eigenvalues,
        eigenvectors,
        diagonalize,
        gradient,
        jacobian,
        hessian,
        laplacian,
        divergence,
        wronskian,
        cyclotomic_polynomial,
        standard_deviation,
        sample_standard_deviation,
    );
    Ok(())
}
