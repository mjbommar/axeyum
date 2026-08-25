//! `axeyum.cas` — combinatorial sequences and the permutation group (tier R).
//!
//! Every sequence here is exact and `i128`-checked: `fibonacci(200)` is `None`,
//! not a wrong number and not an exception. `None` is the honest *outside the
//! `i128` range*, which is a statement about this arithmetic rather than about
//! the mathematics.

use axeyum_cas::Permutation as CasPermutation;
use pyo3::prelude::*;

use crate::stub_types::PyFraction;
use pyo3::types::{PyAny, PyModule};

use crate::cas::rational;

/// Binds `fn(u32) -> Option<i128>`.
macro_rules! sequence {
    ($name:ident, $doc:literal) => {
        #[doc = $doc]
        ///
        /// Tier R: a pure function of `n`. `None` is `i128` overflow, never an
        /// error.
        #[cfg_attr(
            feature = "stub-gen",
            pyo3_stub_gen::derive::gen_stub_pyfunction(module = "axeyum._native.cas")
        )]
        #[pyfunction]
        fn $name(n: u32) -> Option<i128> {
            axeyum_cas::combinatorics::$name(n)
        }
    };
}

/// Binds `fn(u32, u32) -> Option<i128>`.
macro_rules! triangle {
    ($name:ident, $doc:literal) => {
        #[doc = $doc]
        ///
        /// Tier R: a pure function of `n` and `k`. `None` is `i128` overflow.
        #[cfg_attr(
            feature = "stub-gen",
            pyo3_stub_gen::derive::gen_stub_pyfunction(module = "axeyum._native.cas")
        )]
        #[pyfunction]
        fn $name(n: u32, k: u32) -> Option<i128> {
            axeyum_cas::combinatorics::$name(n, k)
        }
    };
}

sequence!(euler_number, "The `n`-th Euler (secant/tangent) number.");
sequence!(
    bell,
    "The `n`-th Bell number: set partitions of `n` elements."
);
sequence!(
    partition_count,
    "The number of integer partitions of `n` (`p(n)`)."
);
sequence!(catalan, "The `n`-th Catalan number.");
sequence!(fibonacci, "The `n`-th Fibonacci number, `F(0) == 0`.");
sequence!(lucas, "The `n`-th Lucas number, `L(0) == 2`.");
sequence!(tribonacci, "The `n`-th tribonacci number.");
sequence!(motzkin, "The `n`-th Motzkin number.");
sequence!(pell, "The `n`-th Pell number.");
sequence!(jacobsthal, "The `n`-th Jacobsthal number.");
sequence!(
    derangements,
    "The number of permutations of `n` with no fixed point (`!n`)."
);
sequence!(double_factorial, "`n!!`, the double factorial.");

triangle!(
    stirling_first,
    "The unsigned Stirling number of the first kind `c(n, k)`."
);
triangle!(
    stirling_second,
    "The Stirling number of the second kind `S(n, k)`."
);
triangle!(narayana, "The Narayana number `N(n, k)`.");
triangle!(lah, "The unsigned Lah number `L(n, k)`.");
triangle!(eulerian, "The Eulerian number `A(n, k)`.");

/// The `n`-th Bernoulli number as an exact `fractions.Fraction`.
///
/// Tier R: a pure function of `n`. `None` is `i128` overflow of the exact
/// rational, never an error.
///
/// The convention is `B(1) == -1/2`.
///
/// # Errors
///
/// Propagates any Python error raised while building the fraction.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyfunction(module = "axeyum._native.cas")
)]
#[pyfunction]
fn bernoulli(py: Python<'_>, n: u32) -> PyResult<Option<PyFraction<'_>>> {
    rational::optional_fraction(py, axeyum_cas::combinatorics::bernoulli(n))
}

/// The `n`-th harmonic number `1 + 1/2 + ... + 1/n` as an exact fraction.
///
/// Tier R: a pure function of `n`. `harmonic(0)` is `0`.
///
/// # Errors
///
/// Propagates any Python error raised while building the fraction.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyfunction(module = "axeyum._native.cas")
)]
#[pyfunction]
fn harmonic(py: Python<'_>, n: u32) -> PyResult<Option<PyFraction<'_>>> {
    rational::optional_fraction(py, axeyum_cas::combinatorics::harmonic(n))
}

/// The generalized harmonic number `sum(1 / k ** r for k in 1..=n)`.
///
/// Tier R: a pure function of `n` and `r`.
///
/// # Errors
///
/// Propagates any Python error raised while building the fraction.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyfunction(module = "axeyum._native.cas")
)]
#[pyfunction]
fn generalized_harmonic(py: Python<'_>, n: u32, r: u32) -> PyResult<Option<PyFraction<'_>>> {
    rational::optional_fraction(py, axeyum_cas::combinatorics::generalized_harmonic(n, r))
}

/// The multinomial coefficient `(sum(groups))! / prod(g! for g in groups)`.
///
/// Tier R: a pure function of `groups`. The empty list is `1`.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyfunction(module = "axeyum._native.cas")
)]
#[pyfunction]
fn multinomial(groups: Vec<u32>) -> Option<i128> {
    axeyum_cas::combinatorics::multinomial(&groups)
}

/// A permutation of `0..n`, stored as its image list.
///
/// Tier R: owned plain data with no budget. Every method that can fail on a
/// shape mismatch returns `None` rather than raising.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyclass(module = "axeyum._native.cas")
)]
#[pyclass(frozen, from_py_object, module = "axeyum", name = "Permutation")]
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Permutation {
    inner: CasPermutation,
}

impl Permutation {
    /// Wraps a Rust permutation.
    fn wrap(inner: CasPermutation) -> Self {
        Self { inner }
    }
}

#[cfg_attr(feature = "stub-gen", pyo3_stub_gen::derive::gen_stub_pymethods)]
#[pymethods]
impl Permutation {
    /// A permutation from its image list, or `None` when the list is not a
    /// bijection of `0..len`.
    #[staticmethod]
    fn from_images(images: Vec<usize>) -> Option<Permutation> {
        CasPermutation::from_images(images).map(Permutation::wrap)
    }

    /// A permutation of `0..n` from disjoint cycles, or `None` when a cycle
    /// repeats a point or leaves the range.
    #[staticmethod]
    fn from_cycles(cycles: Vec<Vec<usize>>, n: usize) -> Option<Permutation> {
        CasPermutation::from_cycles(&cycles, n).map(Permutation::wrap)
    }

    /// The identity on `0..n`.
    #[staticmethod]
    fn identity(n: usize) -> Permutation {
        Permutation::wrap(CasPermutation::identity(n))
    }

    /// The size of the underlying set.
    fn __len__(&self) -> usize {
        self.inner.len()
    }

    /// Whether the permutation acts on the empty set.
    fn is_empty(&self) -> bool {
        self.inner.is_empty()
    }

    /// The image of `point`, or `None` when it is out of range.
    fn apply(&self, point: usize) -> Option<usize> {
        self.inner.apply(point)
    }

    /// `self` after `other`, or `None` on a size mismatch.
    fn compose(&self, other: &Permutation) -> Option<Permutation> {
        self.inner.compose(&other.inner).map(Permutation::wrap)
    }

    /// The inverse permutation.
    fn inverse(&self) -> Permutation {
        Permutation::wrap(self.inner.inverse())
    }

    /// The nontrivial cycles, each starting at its least point.
    fn cycles(&self) -> Vec<Vec<usize>> {
        self.inner.cycles()
    }

    /// The order in the symmetric group, or `None` on `u128` overflow.
    fn order(&self) -> Option<u128> {
        self.inner.order()
    }

    /// The sign: `1` for an even permutation, `-1` for an odd one.
    fn sign(&self) -> i32 {
        self.inner.sign()
    }

    /// The image list.
    #[getter]
    fn images(&self) -> Vec<usize> {
        (0..self.inner.len())
            .map(|point| self.inner.apply(point).unwrap_or(point))
            .collect()
    }

    fn __eq__(&self, other: &Bound<'_, PyAny>) -> bool {
        // `cast` + `get`, never `extract`: `extract` on a `#[pyclass]` CLONES the
        // whole wrapped value to compare it and then drops it.
        other
            .cast::<Permutation>()
            .is_ok_and(|other| other.get().inner == self.inner)
    }

    fn __repr__(&self) -> String {
        format!(
            "Permutation(len={}, sign={})",
            self.inner.len(),
            self.sign()
        )
    }
}

/// Registers the combinatorics surface on `module`.
///
/// # Errors
///
/// Propagates any Python error raised while setting the module attributes.
pub(crate) fn register(module: &Bound<'_, PyModule>) -> PyResult<()> {
    module.add_class::<Permutation>()?;
    macro_rules! add {
        ($($name:ident),* $(,)?) => {
            $(module.add_function(wrap_pyfunction!($name, module)?)?;)*
        };
    }
    add!(
        bernoulli,
        euler_number,
        stirling_first,
        stirling_second,
        bell,
        partition_count,
        catalan,
        fibonacci,
        lucas,
        tribonacci,
        motzkin,
        narayana,
        lah,
        eulerian,
        pell,
        jacobsthal,
        derangements,
        double_factorial,
        multinomial,
        harmonic,
        generalized_harmonic,
    );
    Ok(())
}
