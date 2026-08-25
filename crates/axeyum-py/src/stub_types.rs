//! Python types this crate constructs that `PyO3` has no Rust type for.
//!
//! `pyo3-stub-gen` derives a stub annotation from the Rust return type, so a
//! method returning `Bound<'py, PyAny>` is annotated `typing.Any` however
//! precisely the body knows what it built. Several accessors here build a
//! `fractions.Fraction` or an arbitrary-precision `int` through a concrete
//! constructor and then hand back the untyped handle.
//!
//! The fix is a transparent wrapper per Python type, not a stub override. An
//! override is a second statement of the type, written in a string, checked by
//! nothing; the wrapper puts the claim in the Rust signature where the compiler
//! sees it, and the stub follows from it. The wrapper is a newtype around the
//! same `Bound`, converts by handing that `Bound` straight back, and costs
//! nothing at run time.
//!
//! Neither of them exists in the built extension's Python surface: the
//! conversion is `IntoPyObject`, so what reaches Python is exactly the object
//! the body constructed.

use pyo3::prelude::*;
use pyo3::types::PyAny;

/// A `fractions.Fraction`, exact and arbitrary-precision.
///
/// Every rational this crate returns to Python is one of these; the `i128`
/// reference range lives on the Rust side of the boundary, and a value outside
/// it comes back as `None` rather than as a rounded `Fraction`.
pub(crate) struct PyFraction<'py>(Bound<'py, PyAny>);

impl<'py> PyFraction<'py> {
    /// Wraps an object the caller has already built with `Fraction(...)`.
    pub(crate) fn new(object: Bound<'py, PyAny>) -> Self {
        Self(object)
    }

    /// The wrapped object, for the call sites that need an untyped handle
    /// (building a `dict` value, a heterogeneous list).
    pub(crate) fn into_bound(self) -> Bound<'py, PyAny> {
        self.0
    }
}

impl<'py> IntoPyObject<'py> for PyFraction<'py> {
    type Target = PyAny;
    type Output = Bound<'py, PyAny>;
    type Error = std::convert::Infallible;

    fn into_pyobject(self, _py: Python<'py>) -> Result<Self::Output, Self::Error> {
        Ok(self.0)
    }
}

#[cfg(feature = "stub-gen")]
impl pyo3_stub_gen::PyStubType for PyFraction<'_> {
    fn type_output() -> pyo3_stub_gen::TypeInfo {
        pyo3_stub_gen::TypeInfo::with_module(
            "fractions.Fraction",
            pyo3_stub_gen::ModuleRef::Named("fractions".to_string()),
        )
    }
}

/// An arbitrary-precision Python `int`.
///
/// Used where the value is built through `int.from_bytes` or `int(text, 10)`
/// because it does not fit a machine word: the Python type really is `int`, and
/// annotating it as such is what lets a caller do arithmetic on it without a
/// cast.
pub(crate) struct PyBigInt<'py>(Bound<'py, PyAny>);

impl<'py> PyBigInt<'py> {
    /// Wraps an object the caller has already built as a Python `int`.
    pub(crate) fn new(object: Bound<'py, PyAny>) -> Self {
        Self(object)
    }
}

impl<'py> IntoPyObject<'py> for PyBigInt<'py> {
    type Target = PyAny;
    type Output = Bound<'py, PyAny>;
    type Error = std::convert::Infallible;

    fn into_pyobject(self, _py: Python<'py>) -> Result<Self::Output, Self::Error> {
        Ok(self.0)
    }
}

#[cfg(feature = "stub-gen")]
impl pyo3_stub_gen::PyStubType for PyBigInt<'_> {
    fn type_output() -> pyo3_stub_gen::TypeInfo {
        pyo3_stub_gen::TypeInfo::builtin("int")
    }
}

/// A Python `list` built from a borrowed Rust slice.
///
/// `PyO3` converts `&[T]` to a `list` directly, but `pyo3-stub-gen` has no
/// `PyStubType` for an unsized `[T]` (it cannot: the trait would have to be
/// implemented for a foreign type from a foreign crate), so a getter returning
/// `&[String]` fails to compile under `#[gen_stub_pymethods]`. Widening the
/// return type to `Vec<T>` would type-check by CLONING the collection on every
/// attribute read, which is exactly the copy `docs/python-2026-08/11-zero-copy-audit.md`
/// is about. This wraps the borrow instead: the list is built straight from the
/// slice, and the stub says `list[T]`.
pub(crate) struct PyBorrowedList<'a, T>(pub(crate) &'a [T]);

impl<'py, T> IntoPyObject<'py> for PyBorrowedList<'_, T>
where
    for<'a> &'a T: IntoPyObject<'py>,
{
    type Target = pyo3::types::PyList;
    type Output = Bound<'py, pyo3::types::PyList>;
    type Error = PyErr;

    fn into_pyobject(self, py: Python<'py>) -> Result<Self::Output, Self::Error> {
        pyo3::types::PyList::new(py, self.0)
    }
}

#[cfg(feature = "stub-gen")]
impl<T: pyo3_stub_gen::PyStubType> pyo3_stub_gen::PyStubType for PyBorrowedList<'_, T> {
    fn type_output() -> pyo3_stub_gen::TypeInfo {
        pyo3_stub_gen::TypeInfo::list_of::<T>()
    }
}

/// A Python sequence whose elements are all `T`.
///
/// The bodies here iterate the argument with `try_iter` and convert element by
/// element, so the Rust parameter is `&Bound<'_, PyAny>` and the derived stub
/// says `typing.Any` -- which tells a caller nothing about what may go in it.
/// Extracting a `Vec<T>` instead would fix the stub and NARROW the runtime: `PyO3`
/// requires a real sequence for that, while `try_iter` accepts any iterable, and
/// a generator argument that works today would start raising. This wrapper keeps
/// the iteration and states the element type.
pub(crate) struct PySequence<'py, T>(Bound<'py, PyAny>, std::marker::PhantomData<fn() -> T>);

impl<'py, T> PySequence<'py, T> {
    /// The wrapped object, to iterate exactly as before.
    pub(crate) fn as_any(&self) -> &Bound<'py, PyAny> {
        &self.0
    }
}

impl<'py, T> FromPyObject<'_, 'py> for PySequence<'py, T> {
    type Error = PyErr;

    fn extract(object: pyo3::Borrowed<'_, 'py, PyAny>) -> Result<Self, Self::Error> {
        Ok(Self(object.to_owned(), std::marker::PhantomData))
    }
}

#[cfg(feature = "stub-gen")]
impl<T: pyo3_stub_gen::PyStubType> pyo3_stub_gen::PyStubType for PySequence<'_, T> {
    fn type_input() -> pyo3_stub_gen::TypeInfo {
        // `Vec<T>` already renders `typing.Sequence[T]` on input, with the right
        // imports and cross-module qualification; borrowing it keeps one source
        // of truth for how an element type is spelled.
        <Vec<T> as pyo3_stub_gen::PyStubType>::type_input()
    }

    fn type_output() -> pyo3_stub_gen::TypeInfo {
        <Vec<T> as pyo3_stub_gen::PyStubType>::type_output()
    }
}

/// A `frozenset[T]`.
///
/// `pyo3-stub-gen` has no `PyStubType` for `PyFrozenSet` and every Rust set type
/// maps to a mutable `set`, so a module constant that is genuinely immutable at
/// run time -- `ir.OP_NAMES` is a `frozenset`, on purpose -- is otherwise
/// declared as something a caller could mutate. `stubtest` catches the mismatch;
/// this is what makes the declaration true.
///
/// It exists only to NAME a type -- `module_variable!` takes a Rust type and
/// reads `PyStubType` off it -- so nothing constructs one, and outside the
/// `stub-gen` feature nothing refers to it either.
#[cfg(feature = "stub-gen")]
pub(crate) struct PyFrozenSetOf<T>(std::marker::PhantomData<fn() -> T>);

#[cfg(feature = "stub-gen")]
impl<T: pyo3_stub_gen::PyStubType> pyo3_stub_gen::PyStubType for PyFrozenSetOf<T> {
    fn type_output() -> pyo3_stub_gen::TypeInfo {
        let inner = T::type_output();
        let mut info = pyo3_stub_gen::TypeInfo::builtin(&format!("frozenset[{}]", inner.name));
        info.import.extend(inner.import);
        info
    }
}
