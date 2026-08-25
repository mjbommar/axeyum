//! `axeyum.cas` — matrix normal forms and decompositions (tier R).
//!
//! Every routine here returns the **factors**, never a claim about them: Jordan
//! gives `(P, J)` with `A == P J P^-1`, Smith gives `(U, D, V)` with
//! `U A V == D`, Hermite gives `(U, H)` with `U A == H`. That is deliberate — a
//! caller can multiply the factors back together and check the identity without
//! trusting this code, which a bare "the Jordan form is J" does not allow.
//!
//! `None` is *outside the fragment* (a matrix that does not diagonalize over the
//! rationals, a non-square input, a non-integer matrix for an integer normal
//! form) or exact `i128` overflow.

use pyo3::prelude::*;
use pyo3::types::{PyAny, PyModule};

use crate::cas::expr::Expr;
use crate::cas::functions::Matrix;

/// `(P, J)` with `matrix == P J P^-1`, or `None` when no rational Jordan form
/// exists.
///
/// Tier R: a pure function of its arguments. `var` names the variable the
/// characteristic polynomial is taken in.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyfunction(module = "axeyum._native.cas")
)]
#[pyfunction]
fn jordan_form(py: Python<'_>, matrix: &Matrix, var: &str) -> Option<(Matrix, Matrix)> {
    py.detach(|| axeyum_cas::jordan_form(matrix.inner(), var))
        .map(|(p, j)| (Matrix::wrap(p), Matrix::wrap(j)))
}

/// `exp(matrix * t)` as a matrix of expressions in `t`, or `None`.
///
/// Tier R: a pure function of its arguments.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyfunction(module = "axeyum._native.cas")
)]
#[pyfunction]
fn matrix_exp(py: Python<'_>, matrix: &Matrix, t: &str) -> Option<Matrix> {
    Matrix::wrap_option(py.detach(|| axeyum_cas::matrix_exp(matrix.inner(), t)))
}

/// The solution of `x' == matrix x`, `x(0) == initial`, as a column of
/// expressions in `t`.
///
/// Tier R: a pure function of its arguments.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyfunction(module = "axeyum._native.cas")
)]
#[pyfunction]
fn linear_ode_system(py: Python<'_>, matrix: &Matrix, initial: &Matrix, t: &str) -> Option<Matrix> {
    Matrix::wrap_option(
        py.detach(|| axeyum_cas::linear_ode_system(matrix.inner(), initial.inner(), t)),
    )
}

/// `(U, H)` with `U * matrix == H` in Hermite normal form, or `None`.
///
/// Tier R: a pure function of its argument. `U` is the unimodular transform, so
/// the caller can re-derive `H` rather than take it on faith.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyfunction(module = "axeyum._native.cas")
)]
#[pyfunction]
fn hermite_normal_form(py: Python<'_>, matrix: &Matrix) -> Option<(Matrix, Matrix)> {
    py.detach(|| axeyum_cas::hermite_normal_form(matrix.inner()))
        .map(|(u, h)| (Matrix::wrap(u), Matrix::wrap(h)))
}

/// `(U, D, V)` with `U * matrix * V == D` in Smith normal form, or `None`.
///
/// Tier R: a pure function of its argument. Both transforms are returned for
/// the same reason as [`hermite_normal_form`].
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyfunction(module = "axeyum._native.cas")
)]
#[pyfunction]
fn smith_normal_form(py: Python<'_>, matrix: &Matrix) -> Option<(Matrix, Matrix, Matrix)> {
    py.detach(|| axeyum_cas::smith_normal_form(matrix.inner()))
        .map(|(u, d, v)| (Matrix::wrap(u), Matrix::wrap(d), Matrix::wrap(v)))
}

/// `(Q, R)` with `matrix == Q R`, `Q` orthogonal and `R` upper triangular, or
/// `None` when the exact rational arithmetic cannot produce it.
///
/// Tier R: a pure function of its argument.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyfunction(module = "axeyum._native.cas")
)]
#[pyfunction]
fn qr_decomposition(py: Python<'_>, matrix: &Matrix) -> Option<(Matrix, Matrix)> {
    py.detach(|| axeyum_cas::qr_decomposition(matrix.inner()))
        .map(|(q, r)| (Matrix::wrap(q), Matrix::wrap(r)))
}

/// The lower-triangular `L` with `matrix == L L^T`, or `None` when the matrix is
/// not symmetric positive definite over the exact rationals.
///
/// Tier R: a pure function of its argument.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyfunction(module = "axeyum._native.cas")
)]
#[pyfunction]
fn cholesky_decomposition(py: Python<'_>, matrix: &Matrix) -> Option<Matrix> {
    Matrix::wrap_option(py.detach(|| axeyum_cas::cholesky_decomposition(matrix.inner())))
}

/// The Gram-Schmidt orthogonalization of `vectors`, as a list of lists.
///
/// Tier R: a pure function of its argument. `None` for ragged input or a
/// linearly dependent family.
///
/// # Errors
///
/// Propagates the per-element extraction error.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyfunction(module = "axeyum._native.cas")
)]
#[pyfunction]
fn gram_schmidt(vectors: &Bound<'_, PyAny>) -> PyResult<Option<Vec<Vec<Expr>>>> {
    let mut collected = Vec::new();
    for row in vectors.try_iter()? {
        collected.push(Expr::vec_from_py(&row?)?);
    }
    Ok(axeyum_cas::gram_schmidt(&collected)
        .map(|rows| rows.into_iter().map(Expr::wrap_vec).collect()))
}

/// Registers the normal-form surface on `module`.
///
/// # Errors
///
/// Propagates any Python error raised while setting the module attributes.
pub(crate) fn register(module: &Bound<'_, PyModule>) -> PyResult<()> {
    macro_rules! add {
        ($($name:ident),* $(,)?) => {
            $(module.add_function(wrap_pyfunction!($name, module)?)?;)*
        };
    }
    add!(
        jordan_form,
        matrix_exp,
        linear_ode_system,
        hermite_normal_form,
        smith_normal_form,
        qr_decomposition,
        cholesky_decomposition,
        gram_schmidt,
    );
    Ok(())
}
