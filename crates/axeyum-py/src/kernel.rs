//! `axeyum._native.kernel` — the in-tree Lean kernel, its preludes, and the
//! axiom footprints that make axiom-freedom a *measurement* rather than a claim.
//!
//! # What this module is for
//!
//! CLAUDE.md records that **you cannot read this kernel's theorem inventory from
//! source text**: declarations go through a `.theorem(name, …)` helper taking an
//! interned `NameId`, so grepping `.theorem("…")` returns zero matches against
//! 139 real Nat theorems, and three separate counts of this repository's
//! theorems were wrong before anyone built the environment to look. Five example
//! binaries exist only because there was no other way to ask. This module is
//! that other way: `Kernel().build_nat_prelude()` and then ordinary Python over
//! `declarations()`, `axiom_footprint()` and `render_lean()`.
//!
//! # The one non-negotiable invariant: handle provenance
//!
//! `NameId`, `LevelId` and `ExprId` are lifetime-free `Copy` indices into *the
//! kernel that interned them*. Rust does not stop you mixing kernels; nothing
//! does. `kernel_a.render_lean(expr_from_kernel_b)` renders a **different term**
//! and says nothing about it. So every handle this module hands out carries the
//! producing kernel's epoch, and every call that consumes one checks it and
//! raises [`EpochError`]. [`PyKernel::fork`] deliberately takes a **new** epoch:
//! a fork is a snapshot whose future divergence makes the parent's handles
//! unsafe to trust, and refusing them up front is cheaper than a silent
//! disagreement later.
//!
//! # Nothing found is not the same as not looked at
//!
//! `Kernel::axiom_footprint` returns an empty vector for an **absent** name —
//! byte-identical to the answer for an axiom-free theorem, which is this
//! project's headline claim. Every accessor here checks the environment first
//! and raises `KeyError`, and `is_axiom_free` is defined only through
//! `axiom_footprint`, never by a `Declaration::Axiom` variant test (the trusted
//! surface is `Axiom | Opaque | Quotient`; a lane already got that wrong).

mod prelude_fields;

use std::collections::HashMap;
use std::sync::atomic::{AtomicU64, Ordering};

use axeyum_lean_import as lean_import;
use axeyum_lean_kernel::{
    BinderInfo, Declaration, ExprId, ExprNode, Kernel, KernelError as RustKernelError,
    Lean4ExportMetadata, LevelId, Lit, LogicPrelude, NameId, NameNode, NatLit, ReducibilityHint,
    build_arith_prelude, build_complex_prelude, build_cpoint_prelude, build_creal_prelude,
    build_int_prelude, build_logic_prelude, build_nat_prelude, build_rat_prelude,
    build_string_prelude, prelude_cache,
};
use pyo3::create_exception;
use pyo3::exceptions::{PyAttributeError, PyKeyError, PyTypeError, PyValueError};
use pyo3::prelude::*;
use pyo3::types::{PyDict, PyInt, PyList, PyModule, PyTuple};

use crate::error::{AxeyumError, InternalError};
use prelude_fields::Sub;

create_exception!(
    axeyum,
    EpochError,
    AxeyumError,
    "A handle was used with a kernel that did not intern it.\n\n`NameId`, `LevelId` and `ExprId` are lifetime-free indices into one kernel's\ntables. Passing one to another kernel is not a type error in Rust -- it silently\ndenotes a DIFFERENT term. This exception is the binding refusing to do that."
);

create_exception!(
    axeyum,
    KernelError,
    AxeyumError,
    "The kernel refused a declaration, an inference, or an inductive.\n\nOne class, not 60: the Rust `KernelError` is a large struct-variant enum and a\nproducer branches on WHICH rejection it got. The variant name is carried as\n`.variant` and its payload as `.fields`; `.names` renders any payload name that\nresolves to a declaration in the environment. Never match on the message text."
);

/// Process-wide source of kernel epochs.
///
/// Starts at 1 so that 0 is never a live epoch and a default-initialized handle
/// cannot accidentally validate.
static NEXT_EPOCH: AtomicU64 = AtomicU64::new(1);

/// The next unused kernel epoch.
fn next_epoch() -> u64 {
    NEXT_EPOCH.fetch_add(1, Ordering::Relaxed)
}

/// Refuses a handle interned by a different kernel.
fn epoch_guard(kernel_epoch: u64, handle_epoch: u64, kind: &str) -> PyResult<()> {
    if kernel_epoch == handle_epoch {
        return Ok(());
    }
    Err(EpochError::new_err(format!(
        "{kind} was interned by kernel epoch {handle_epoch}, but this kernel is epoch \
         {kernel_epoch}. Handles are indices into one kernel's tables: using this one here \
         would denote a different term, not raise an error in Rust."
    )))
}

// ---------------------------------------------------------------------------
// Handles
// ---------------------------------------------------------------------------

/// An interned hierarchical name, valid only in the kernel that interned it.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyclass(module = "axeyum._native.kernel")
)]
#[pyclass(frozen, from_py_object, module = "axeyum", name = "NameId")]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct PyNameId {
    /// The interning kernel's epoch.
    epoch: u64,
    /// The interned handle.
    id: NameId,
}

#[cfg_attr(feature = "stub-gen", pyo3_stub_gen::derive::gen_stub_pymethods)]
#[pymethods]
impl PyNameId {
    /// The epoch of the kernel that interned this name.
    #[getter]
    fn epoch(&self) -> u64 {
        self.epoch
    }

    /// The handle's dense index in its kernel's name table.
    #[getter]
    fn raw(&self) -> usize {
        self.id.index()
    }

    fn __repr__(&self) -> String {
        format!("NameId(raw={}, epoch={})", self.id.index(), self.epoch)
    }

    // `&Bound<'_, PyAny>`, not `&Self`: `__eq__` must accept ANY object.
    // Typed as `&Self` it raises TypeError on a mismatch, where Python expects
    // `False`, and the derived stub then declares `__eq__(self, other: Self)`,
    // which mypy rejects as a Liskov violation against `object.__eq__` -- the
    // stub package fails to BUILD, so `stubtest` compares nothing at all.
    fn __eq__(&self, other: &Bound<'_, PyAny>) -> bool {
        other
            .cast::<Self>()
            .is_ok_and(|other| self.epoch == other.get().epoch && self.id == other.get().id)
    }

    fn __hash__(&self) -> u64 {
        self.epoch.rotate_left(32) ^ self.id.index() as u64
    }
}

/// An interned universe level, valid only in the kernel that interned it.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyclass(module = "axeyum._native.kernel")
)]
#[pyclass(frozen, from_py_object, module = "axeyum", name = "LevelId")]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct PyLevelId {
    /// The interning kernel's epoch.
    epoch: u64,
    /// The interned handle.
    id: LevelId,
}

#[cfg_attr(feature = "stub-gen", pyo3_stub_gen::derive::gen_stub_pymethods)]
#[pymethods]
impl PyLevelId {
    /// The epoch of the kernel that interned this level.
    #[getter]
    fn epoch(&self) -> u64 {
        self.epoch
    }

    /// The handle's dense index in its kernel's level table.
    #[getter]
    fn raw(&self) -> usize {
        self.id.index()
    }

    fn __repr__(&self) -> String {
        format!("LevelId(raw={}, epoch={})", self.id.index(), self.epoch)
    }

    // `&Bound<'_, PyAny>`, not `&Self`: `__eq__` must accept ANY object.
    // Typed as `&Self` it raises TypeError on a mismatch, where Python expects
    // `False`, and the derived stub then declares `__eq__(self, other: Self)`,
    // which mypy rejects as a Liskov violation against `object.__eq__` -- the
    // stub package fails to BUILD, so `stubtest` compares nothing at all.
    fn __eq__(&self, other: &Bound<'_, PyAny>) -> bool {
        other
            .cast::<Self>()
            .is_ok_and(|other| self.epoch == other.get().epoch && self.id == other.get().id)
    }

    fn __hash__(&self) -> u64 {
        self.epoch.rotate_left(32) ^ self.id.index() as u64
    }
}

/// An interned expression, valid only in the kernel that interned it.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyclass(module = "axeyum._native.kernel")
)]
#[pyclass(frozen, from_py_object, module = "axeyum", name = "ExprId")]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct PyExprId {
    /// The interning kernel's epoch.
    epoch: u64,
    /// The interned handle.
    id: ExprId,
}

#[cfg_attr(feature = "stub-gen", pyo3_stub_gen::derive::gen_stub_pymethods)]
#[pymethods]
impl PyExprId {
    /// The epoch of the kernel that interned this expression.
    #[getter]
    fn epoch(&self) -> u64 {
        self.epoch
    }

    /// The handle's dense index in its kernel's expression arena.
    #[getter]
    fn raw(&self) -> usize {
        self.id.index()
    }

    fn __repr__(&self) -> String {
        format!("ExprId(raw={}, epoch={})", self.id.index(), self.epoch)
    }

    // `&Bound<'_, PyAny>`, not `&Self`: `__eq__` must accept ANY object.
    // Typed as `&Self` it raises TypeError on a mismatch, where Python expects
    // `False`, and the derived stub then declares `__eq__(self, other: Self)`,
    // which mypy rejects as a Liskov violation against `object.__eq__` -- the
    // stub package fails to BUILD, so `stubtest` compares nothing at all.
    fn __eq__(&self, other: &Bound<'_, PyAny>) -> bool {
        other
            .cast::<Self>()
            .is_ok_and(|other| self.epoch == other.get().epoch && self.id == other.get().id)
    }

    fn __hash__(&self) -> u64 {
        self.epoch.rotate_left(32) ^ self.id.index() as u64
    }
}

// ---------------------------------------------------------------------------
// Binder info and literals
// ---------------------------------------------------------------------------

/// The binder annotation on a `lam`/`pi` binder.
///
/// These mirror Lean's binder brackets. They are elaboration and printing
/// metadata: they do **not** affect type checking or definitional equality, so
/// two terms differing only here are `def_eq`.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyclass_enum(module = "axeyum._native.kernel")
)]
#[pyclass(eq, eq_int, from_py_object, module = "axeyum", name = "BinderInfo")]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PyBinderInfo {
    /// `(x : T)` — an ordinary explicit binder.
    Default,
    /// `{x : T}` — an implicit binder.
    Implicit,
    /// `{{x : T}}` — a strict implicit binder.
    StrictImplicit,
    /// `[x : T]` — an instance-implicit (type-class) binder.
    InstImplicit,
}

impl From<PyBinderInfo> for BinderInfo {
    fn from(value: PyBinderInfo) -> Self {
        match value {
            PyBinderInfo::Default => Self::Default,
            PyBinderInfo::Implicit => Self::Implicit,
            PyBinderInfo::StrictImplicit => Self::StrictImplicit,
            PyBinderInfo::InstImplicit => Self::InstImplicit,
        }
    }
}

impl From<BinderInfo> for PyBinderInfo {
    fn from(value: BinderInfo) -> Self {
        match value {
            BinderInfo::Default => Self::Default,
            BinderInfo::Implicit => Self::Implicit,
            BinderInfo::StrictImplicit => Self::StrictImplicit,
            BinderInfo::InstImplicit => Self::InstImplicit,
        }
    }
}

/// A literal embeddable in an expression: an arbitrary-precision natural, or a
/// string.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyclass(module = "axeyum._native.kernel")
)]
#[pyclass(frozen, from_py_object, module = "axeyum", name = "Lit")]
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PyLit {
    /// The wrapped literal.
    inner: Lit,
}

#[cfg_attr(feature = "stub-gen", pyo3_stub_gen::derive::gen_stub_pymethods)]
#[pymethods]
impl PyLit {
    /// A natural-number literal, with no fixed-width ceiling.
    ///
    /// The value crosses the boundary as its canonical base-10 spelling, so a
    /// Python `int` of any size round-trips exactly; there is no `u64` step to
    /// silently truncate at.
    ///
    /// # Errors
    ///
    /// Raises `ValueError` for a negative value.
    #[staticmethod]
    fn nat(value: &Bound<'_, PyAny>) -> PyResult<Self> {
        let decimal: String = value.str()?.extract()?;
        let parsed = NatLit::from_decimal(&decimal).ok_or_else(|| {
            PyValueError::new_err(format!(
                "Lit.nat needs a non-negative integer, got {decimal:?}"
            ))
        })?;
        Ok(Self {
            inner: Lit::Nat(parsed),
        })
    }

    /// A string literal.
    #[staticmethod]
    #[pyo3(name = "str")]
    fn str_(value: String) -> Self {
        Self {
            inner: Lit::Str(value),
        }
    }

    /// `"nat"` or `"str"`.
    #[getter]
    fn kind(&self) -> &'static str {
        match &self.inner {
            Lit::Nat(_) => "nat",
            Lit::Str(_) => "str",
        }
    }

    /// The literal's value: a Python `int` for a natural, a `str` for a string.
    ///
    /// # Errors
    ///
    /// Propagates any Python error raised while building the value.
    #[getter]
    fn value<'py>(&self, py: Python<'py>) -> PyResult<Bound<'py, PyAny>> {
        match &self.inner {
            Lit::Nat(n) => py.get_type::<PyInt>().call1((n.to_string(), 10u8)),
            Lit::Str(s) => Ok(s.into_pyobject(py)?.into_any()),
        }
    }

    fn __repr__(&self) -> String {
        match &self.inner {
            Lit::Nat(n) => format!("Lit.nat({n})"),
            Lit::Str(s) => format!("Lit.str({s:?})"),
        }
    }

    // `&Bound<'_, PyAny>`, not `&Self`: `__eq__` must accept ANY object.
    // Typed as `&Self` it raises TypeError on a mismatch, where Python expects
    // `False`, and the derived stub then declares `__eq__(self, other: Self)`,
    // which mypy rejects as a Liskov violation against `object.__eq__` -- the
    // stub package fails to BUILD, so `stubtest` compares nothing at all.
    fn __eq__(&self, other: &Bound<'_, PyAny>) -> bool {
        other
            .cast::<Self>()
            .is_ok_and(|other| self.inner == other.get().inner)
    }
}

// ---------------------------------------------------------------------------
// Expression nodes
// ---------------------------------------------------------------------------

/// One destructured expression node, copied out of the kernel arena.
///
/// The Rust `expr_node` returns a **borrow** into the kernel; a borrow cannot
/// cross into Python, and holding one would pin the kernel against the `&mut
/// self` every constructor needs. So this is an owned copy: reading it can never
/// observe a later mutation, which is the honest shape for a snapshot.
///
/// Accessors that do not apply to `kind` return `None` rather than raising —
/// `node.name if node.kind == "const" else ...` is the intended idiom, and
/// [`Self::args`] gives the whole payload as a tuple for destructuring.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyclass(module = "axeyum._native.kernel")
)]
#[pyclass(frozen, skip_from_py_object, module = "axeyum", name = "ExprNode")]
#[derive(Debug, Clone)]
pub struct PyExprNode {
    /// The variant tag.
    kind: &'static str,
    /// `BVar`'s de Bruijn index.
    index: Option<u32>,
    /// `FVar`'s unique id.
    fvar_id: Option<u64>,
    /// `Sort`'s universe level.
    level: Option<PyLevelId>,
    /// The name of a `Const`, `Proj` type, or binder.
    name: Option<PyNameId>,
    /// `Const`'s universe arguments.
    levels: Option<Vec<PyLevelId>>,
    /// `Proj`'s zero-based field index.
    field_index: Option<u32>,
    /// `App`'s function.
    fun: Option<PyExprId>,
    /// `App`'s argument.
    arg: Option<PyExprId>,
    /// A binder's domain, or a `let`'s type.
    ty: Option<PyExprId>,
    /// A binder's or `let`'s body.
    body: Option<PyExprId>,
    /// A `let`'s bound value.
    value: Option<PyExprId>,
    /// `Proj`'s projected structure.
    structure: Option<PyExprId>,
    /// A binder's annotation.
    binder: Option<PyBinderInfo>,
    /// `Lit`'s payload.
    lit: Option<PyLit>,
}

#[cfg_attr(feature = "stub-gen", pyo3_stub_gen::derive::gen_stub_pymethods)]
#[pymethods]
impl PyExprNode {
    /// One of `bvar`, `fvar`, `sort`, `const`, `proj`, `app`, `lam`, `pi`,
    /// `let`, `lit`.
    #[getter]
    fn kind(&self) -> &'static str {
        self.kind
    }

    /// A `bvar`'s de Bruijn index (0 = innermost binder).
    #[getter]
    fn index(&self) -> Option<u32> {
        self.index
    }

    /// An `fvar`'s unique id.
    #[getter]
    fn fvar_id(&self) -> Option<u64> {
        self.fvar_id
    }

    /// A `sort`'s universe level.
    #[getter]
    fn level(&self) -> Option<PyLevelId> {
        self.level
    }

    /// The name of a `const`, a `proj`'s structure type, or a binder.
    #[getter]
    fn name(&self) -> Option<PyNameId> {
        self.name
    }

    /// A `const`'s universe arguments.
    #[getter]
    fn levels<'py>(&self, py: Python<'py>) -> PyResult<Option<Bound<'py, PyList>>> {
        // Built straight from the iterator rather than cloned into a `Vec` that
        // `PyO3` would immediately walk again; `&PyLevelId` has no
        // `IntoPyObject`, so a borrow is not an option here.
        self.levels
            .as_deref()
            .map(|levels| PyList::new(py, levels.iter().copied()))
            .transpose()
    }

    /// A `proj`'s zero-based field index (constructor parameters excluded).
    #[getter]
    fn field_index(&self) -> Option<u32> {
        self.field_index
    }

    /// An `app`'s function.
    #[getter]
    fn fun(&self) -> Option<PyExprId> {
        self.fun
    }

    /// An `app`'s argument.
    #[getter]
    fn arg(&self) -> Option<PyExprId> {
        self.arg
    }

    /// A binder's domain, or a `let`'s declared type.
    #[getter]
    fn ty(&self) -> Option<PyExprId> {
        self.ty
    }

    /// A binder's or `let`'s body.
    #[getter]
    fn body(&self) -> Option<PyExprId> {
        self.body
    }

    /// A `let`'s bound value.
    #[getter]
    fn value(&self) -> Option<PyExprId> {
        self.value
    }

    /// A `proj`'s projected structure expression.
    #[getter]
    fn structure(&self) -> Option<PyExprId> {
        self.structure
    }

    /// A binder's annotation.
    #[getter]
    fn binder(&self) -> Option<PyBinderInfo> {
        self.binder
    }

    /// A `lit`'s payload.
    #[getter]
    fn lit(&self) -> Option<PyLit> {
        self.lit.clone()
    }

    /// The variant's payload, in the order the Rust variant declares it.
    ///
    /// # Errors
    ///
    /// Propagates any Python error raised while building the tuple.
    fn args<'py>(&self, py: Python<'py>) -> PyResult<Bound<'py, PyTuple>> {
        let tuple = match self.kind {
            "bvar" => (self.index,).into_pyobject(py)?,
            "fvar" => (self.fvar_id,).into_pyobject(py)?,
            "sort" => (self.level,).into_pyobject(py)?,
            "const" => (self.name, self.levels.clone()).into_pyobject(py)?,
            "proj" => (self.name, self.field_index, self.structure).into_pyobject(py)?,
            "app" => (self.fun, self.arg).into_pyobject(py)?,
            "lam" | "pi" => (self.name, self.ty, self.body, self.binder).into_pyobject(py)?,
            "let" => (self.name, self.ty, self.value, self.body).into_pyobject(py)?,
            _ => (self.lit.clone(),).into_pyobject(py)?,
        };
        Ok(tuple)
    }

    fn __repr__(&self) -> String {
        format!("ExprNode(kind={:?})", self.kind)
    }
}

impl PyExprNode {
    /// An all-`None` node of the given kind.
    fn blank(kind: &'static str) -> Self {
        Self {
            kind,
            index: None,
            fvar_id: None,
            level: None,
            name: None,
            levels: None,
            field_index: None,
            fun: None,
            arg: None,
            ty: None,
            body: None,
            value: None,
            structure: None,
            binder: None,
            lit: None,
        }
    }
}

// ---------------------------------------------------------------------------
// Declarations
// ---------------------------------------------------------------------------

/// One declaration — the unit `add_declaration` admits and the environment
/// stores.
///
/// The **trusted surface is `Axiom | Opaque | Quotient`**, not `Axiom` alone:
/// an `Opaque` has no proof body available for definitional unfolding and the
/// quotient package admits `Quot.sound`. Do not test `kind == "axiom"` to decide
/// whether something rests on assumptions; ask
/// [`PyKernel::axiom_footprint`].
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyclass(module = "axeyum._native.kernel")
)]
#[pyclass(frozen, skip_from_py_object, module = "axeyum", name = "Declaration")]
#[derive(Debug, Clone)]
pub struct PyDeclaration {
    /// The epoch of the kernel whose handles this declaration names.
    epoch: u64,
    /// The wrapped declaration.
    inner: Declaration,
}

/// The epoch shared by a declaration's handles, or an error if they disagree.
fn shared_epoch(name: PyNameId, uparams: &[PyNameId], exprs: &[PyExprId]) -> PyResult<u64> {
    let epoch = name.epoch;
    for uparam in uparams {
        epoch_guard(epoch, uparam.epoch, "universe parameter NameId")?;
    }
    for expr in exprs {
        epoch_guard(epoch, expr.epoch, "ExprId")?;
    }
    Ok(epoch)
}

// PyO3 extracts OWNED values across the FFI edge: a `&[T]` or a `&PyRef<T>`
// cannot be built from a Python object, so every argument below is by value
// whether or not the body consumes it.
#[allow(clippy::needless_pass_by_value)]
#[cfg_attr(feature = "stub-gen", pyo3_stub_gen::derive::gen_stub_pymethods)]
#[pymethods]
impl PyDeclaration {
    /// `axiom name : ty` — an asserted constant with no definitional value.
    ///
    /// # Errors
    ///
    /// Raises `EpochError` if the handles come from different kernels.
    #[staticmethod]
    fn axiom(name: PyNameId, uparams: Vec<PyNameId>, ty: PyExprId) -> PyResult<Self> {
        let epoch = shared_epoch(name, &uparams, &[ty])?;
        Ok(Self {
            epoch,
            inner: Declaration::Axiom {
                name: name.id,
                uparams: uparams.iter().map(|u| u.id).collect(),
                ty: ty.id,
            },
        })
    }

    /// `def name : ty := value`.
    ///
    /// `hint` is the reducibility hint driving lazy-delta unfolding order:
    /// `"regular"` (with `height`), `"abbrev"` (always unfold first) or
    /// `"opaque"` (never preferred). It is a performance-shaped choice, not a
    /// soundness one.
    ///
    /// # Errors
    ///
    /// Raises `EpochError` if the handles come from different kernels, and
    /// `ValueError` for an unknown `hint`.
    #[staticmethod]
    #[pyo3(signature = (name, uparams, ty, value, hint = "regular", height = 0))]
    fn definition(
        name: PyNameId,
        uparams: Vec<PyNameId>,
        ty: PyExprId,
        value: PyExprId,
        hint: &str,
        height: u16,
    ) -> PyResult<Self> {
        let epoch = shared_epoch(name, &uparams, &[ty, value])?;
        let hint = match hint {
            "regular" => ReducibilityHint::Regular(height),
            "abbrev" => ReducibilityHint::Abbrev,
            "opaque" => ReducibilityHint::Opaque,
            other => {
                return Err(PyValueError::new_err(format!(
                    "hint must be \"regular\", \"abbrev\" or \"opaque\", got {other:?}"
                )));
            }
        };
        Ok(Self {
            epoch,
            inner: Declaration::Definition {
                name: name.id,
                uparams: uparams.iter().map(|u| u.id).collect(),
                ty: ty.id,
                value: value.id,
                hint,
            },
        })
    }

    /// `theorem name : ty := value`.
    ///
    /// # Errors
    ///
    /// Raises `EpochError` if the handles come from different kernels.
    #[staticmethod]
    fn theorem(
        name: PyNameId,
        uparams: Vec<PyNameId>,
        ty: PyExprId,
        value: PyExprId,
    ) -> PyResult<Self> {
        let epoch = shared_epoch(name, &uparams, &[ty, value])?;
        Ok(Self {
            epoch,
            inner: Declaration::Theorem {
                name: name.id,
                uparams: uparams.iter().map(|u| u.id).collect(),
                ty: ty.id,
                value: value.id,
            },
        })
    }

    /// `opaque name : ty := value` — checked at admission, never unfolded.
    ///
    /// # Errors
    ///
    /// Raises `EpochError` if the handles come from different kernels.
    #[staticmethod]
    fn opaque(
        name: PyNameId,
        uparams: Vec<PyNameId>,
        ty: PyExprId,
        value: PyExprId,
    ) -> PyResult<Self> {
        let epoch = shared_epoch(name, &uparams, &[ty, value])?;
        Ok(Self {
            epoch,
            inner: Declaration::Opaque {
                name: name.id,
                uparams: uparams.iter().map(|u| u.id).collect(),
                ty: ty.id,
                value: value.id,
            },
        })
    }

    /// One of `axiom`, `definition`, `theorem`, `opaque`, `inductive`,
    /// `constructor`, `recursor`, `quotient`.
    #[getter]
    fn kind(&self) -> &'static str {
        match &self.inner {
            Declaration::Axiom { .. } => "axiom",
            Declaration::Definition { .. } => "definition",
            Declaration::Theorem { .. } => "theorem",
            Declaration::Opaque { .. } => "opaque",
            Declaration::Inductive { .. } => "inductive",
            Declaration::Constructor { .. } => "constructor",
            Declaration::Recursor { .. } => "recursor",
            Declaration::Quotient { .. } => "quotient",
        }
    }

    /// The declared name.
    #[getter]
    fn name(&self) -> PyNameId {
        PyNameId {
            epoch: self.epoch,
            id: self.inner.name(),
        }
    }

    /// The universe parameters this declaration is polymorphic over.
    #[getter]
    fn uparams(&self) -> Vec<PyNameId> {
        self.inner
            .uparams()
            .iter()
            .map(|&id| PyNameId {
                epoch: self.epoch,
                id,
            })
            .collect()
    }

    /// The declared (closed) type.
    #[getter]
    fn ty(&self) -> PyExprId {
        PyExprId {
            epoch: self.epoch,
            id: self.inner.ty(),
        }
    }

    /// The declared value, when the variant has one.
    #[getter]
    fn value(&self) -> Option<PyExprId> {
        self.inner.value().map(|id| PyExprId {
            epoch: self.epoch,
            id,
        })
    }

    /// The epoch of the kernel whose handles this declaration names.
    #[getter]
    fn epoch(&self) -> u64 {
        self.epoch
    }

    fn __repr__(&self) -> String {
        format!(
            "Declaration(kind={:?}, name=NameId(raw={}), epoch={})",
            self.kind(),
            self.inner.name().index(),
            self.epoch
        )
    }
}

// ---------------------------------------------------------------------------
// Prelude packages
// ---------------------------------------------------------------------------

/// A prelude package: the bundle of interned names a `build_*_prelude` call
/// returns.
///
/// The Rust packages are plain structs with up to 244 `NameId` fields each
/// (1,207 across the nine), so the Python view is a flat, ordered
/// `{field name -> NameId}` table reached by attribute access:
/// `nat.add_comm`, `nat.logic.eq_refl`. The field list is generated from the
/// struct definitions by `scripts/gen-py-prelude-fields.py`; a hand-written one
/// would rot into a *missing* attribute, which reads exactly like "that theorem
/// does not exist".
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyclass(module = "axeyum._native.kernel")
)]
#[pyclass(frozen, module = "axeyum", name = "Prelude")]
pub struct PyPrelude {
    /// The package's short kind (`nat`, `logic`, `axreal`, …).
    kind: &'static str,
    /// The owning kernel's epoch.
    epoch: u64,
    /// `(field, name)` in struct declaration order.
    names: Vec<(&'static str, NameId)>,
    /// `(field, names)` for list-valued fields.
    lists: Vec<(&'static str, Vec<NameId>)>,
    /// Sub-packages by field name.
    subs: Vec<(&'static str, Py<PyPrelude>)>,
    /// Field name to position in `names`.
    index: HashMap<&'static str, usize>,
    /// The `LogicPrelude` payload, kept so it can be handed back to
    /// `build_string_prelude`, which is the one builder that takes a
    /// caller-held package.
    logic: Option<Box<LogicPrelude>>,
}

#[cfg_attr(feature = "stub-gen", pyo3_stub_gen::derive::gen_stub_pymethods)]
#[pymethods]
impl PyPrelude {
    /// The package's kind: `logic`, `nat`, `int`, `rat`, `axreal`, `creal`,
    /// `complex`, `cpoint`, or `string`.
    ///
    /// `axreal` — never `real`. The axiomatized ordered field `AxReal` is this
    /// repository's only nonzero axiom row (30 declared, none reached by a
    /// shipped route); the constructed reals `CReal` measure 0. A substring test
    /// for `"Real."` matches `"CReal."`, so classify a carrier by its
    /// declaration, never by a substring.
    #[getter]
    fn kind(&self) -> &'static str {
        self.kind
    }

    /// The owning kernel's epoch.
    #[getter]
    fn epoch(&self) -> u64 {
        self.epoch
    }

    /// Every scalar field name, in struct declaration order.
    #[getter]
    fn field_names(&self) -> Vec<&'static str> {
        self.names.iter().map(|(field, _)| *field).collect()
    }

    /// Every sub-package field name (`nat.logic`, `complex.creal`, …).
    #[getter]
    fn package_names(&self) -> Vec<&'static str> {
        self.subs.iter().map(|(field, _)| *field).collect()
    }

    /// Every list-valued field name.
    #[getter]
    fn list_names(&self) -> Vec<&'static str> {
        self.lists.iter().map(|(field, _)| *field).collect()
    }

    /// The scalar fields as an insertion-ordered `{field: NameId}` dictionary.
    ///
    /// # Errors
    ///
    /// Propagates any Python error raised while building the dictionary.
    fn to_dict<'py>(&self, py: Python<'py>) -> PyResult<Bound<'py, PyDict>> {
        let dict = PyDict::new(py);
        for (field, id) in &self.names {
            dict.set_item(
                field,
                PyNameId {
                    epoch: self.epoch,
                    id: *id,
                },
            )?;
        }
        Ok(dict)
    }

    /// Field lookup: a `NameId`, a sub-`Prelude`, or a `list[NameId]`.
    ///
    /// # Errors
    ///
    /// Raises `AttributeError` for a field this package does not have.
    fn __getattr__<'py>(&self, py: Python<'py>, name: &str) -> PyResult<Bound<'py, PyAny>> {
        if let Some(position) = self.index.get(name) {
            return Ok(PyNameId {
                epoch: self.epoch,
                id: self.names[*position].1,
            }
            .into_pyobject(py)?
            .into_any());
        }
        if let Some((_, sub)) = self.subs.iter().find(|(field, _)| *field == name) {
            return Ok(sub.bind(py).clone().into_any());
        }
        if let Some((_, ids)) = self.lists.iter().find(|(field, _)| *field == name) {
            let wrapped: Vec<PyNameId> = ids
                .iter()
                .map(|&id| PyNameId {
                    epoch: self.epoch,
                    id,
                })
                .collect();
            return Ok(wrapped.into_pyobject(py)?.into_any());
        }
        Err(PyAttributeError::new_err(format!(
            "the {} prelude package has no field {name:?} ({} scalar fields, {} sub-packages)",
            self.kind,
            self.names.len(),
            self.subs.len()
        )))
    }

    /// Field lookup by subscript, identical to attribute access.
    ///
    /// # Errors
    ///
    /// Raises `KeyError` for a field this package does not have.
    fn __getitem__<'py>(&self, py: Python<'py>, name: &str) -> PyResult<Bound<'py, PyAny>> {
        self.__getattr__(py, name)
            .map_err(|_| PyKeyError::new_err(name.to_owned()))
    }

    /// Whether this package has the named field (scalar, list, or sub-package).
    fn __contains__(&self, name: &str) -> bool {
        self.index.contains_key(name)
            || self.subs.iter().any(|(field, _)| *field == name)
            || self.lists.iter().any(|(field, _)| *field == name)
    }

    /// The number of scalar name fields.
    fn __len__(&self) -> usize {
        self.names.len()
    }

    fn __repr__(&self) -> String {
        format!(
            "Prelude(kind={:?}, names={}, packages={}, epoch={})",
            self.kind,
            self.names.len(),
            self.subs.len(),
            self.epoch
        )
    }
}

/// Wraps one package's field table as a Python object.
fn make_prelude(
    py: Python<'_>,
    epoch: u64,
    kind: &'static str,
    fields: prelude_fields::Fields,
    subs: Vec<(&'static str, Sub)>,
    logic: Option<Box<LogicPrelude>>,
) -> PyResult<Py<PyPrelude>> {
    let index = fields
        .names
        .iter()
        .enumerate()
        .map(|(position, (field, _))| (*field, position))
        .collect();
    let mut wrapped = Vec::with_capacity(subs.len());
    for (field, sub) in subs {
        wrapped.push((field, sub_prelude(py, epoch, sub)?));
    }
    Py::new(
        py,
        PyPrelude {
            kind,
            epoch,
            names: fields.names,
            lists: fields.lists,
            subs: wrapped,
            index,
            logic,
        },
    )
}

/// Wraps a nested package.
fn sub_prelude(py: Python<'_>, epoch: u64, sub: Sub) -> PyResult<Py<PyPrelude>> {
    match sub {
        Sub::Logic(p) => make_prelude(
            py,
            epoch,
            "logic",
            prelude_fields::logic(&p),
            Vec::new(),
            Some(p),
        ),
        Sub::Nat(p) => make_prelude(
            py,
            epoch,
            "nat",
            prelude_fields::nat(&p),
            prelude_fields::nat_sub(&p),
            None,
        ),
        Sub::Int(p) => make_prelude(
            py,
            epoch,
            "int",
            prelude_fields::int(&p),
            prelude_fields::int_sub(&p),
            None,
        ),
        Sub::Rat(p) => make_prelude(
            py,
            epoch,
            "rat",
            prelude_fields::rat(&p),
            prelude_fields::rat_sub(&p),
            None,
        ),
        Sub::CReal(p) => make_prelude(
            py,
            epoch,
            "creal",
            prelude_fields::creal(&p),
            prelude_fields::creal_sub(&p),
            None,
        ),
    }
}

/// The process-wide prelude reuse counters (ADR-0464).
///
/// These exist so a gate can distinguish "reuse changed nothing" from "reuse
/// never ran" — indistinguishable from output alone, and this repository has
/// shipped several gates that passed over zero work.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyclass(module = "axeyum._native.kernel")
)]
#[pyclass(
    frozen,
    skip_from_py_object,
    module = "axeyum",
    name = "PreludeCacheStats"
)]
#[derive(Debug, Clone, Copy)]
pub struct PyPreludeCacheStats {
    /// Restorations served from a template kernel.
    #[pyo3(get)]
    hits: u64,
    /// Calls that took the ordinary build path.
    #[pyo3(get)]
    misses: u64,
    /// Templates constructed, at most one per prelude key per process.
    #[pyo3(get)]
    templates_built: u64,
}

#[cfg_attr(feature = "stub-gen", pyo3_stub_gen::derive::gen_stub_pymethods)]
#[pymethods]
impl PyPreludeCacheStats {
    fn __repr__(&self) -> String {
        format!(
            "PreludeCacheStats(hits={}, misses={}, templates_built={})",
            self.hits, self.misses, self.templates_built
        )
    }
}

// ---------------------------------------------------------------------------
// KernelError projection
// ---------------------------------------------------------------------------

/// Splits a `Debug`-rendered struct variant into `(variant, [(field, value)])`.
///
/// The Rust `KernelError` is a 60-variant struct-variant enum with no `Display`
/// impl, and a producer branches on **which** rejection it got. Sixty exception
/// classes would be worse: the variant is data, so it is carried as data. The
/// payload shapes are small and closed (`NameId(7)`, `Some(NameId(7))`, integers,
/// `QuotKind`), which is what makes reading them off `Debug` sound here.
fn split_debug(debug: &str) -> (String, Vec<(String, String)>) {
    let Some(brace) = debug.find(" { ") else {
        return (debug.trim().to_owned(), Vec::new());
    };
    let variant = debug[..brace].trim().to_owned();
    let body = debug[brace + 3..].trim_end().trim_end_matches('}').trim();
    (variant, split_fields(body))
}

/// Splits `a: 1, b: Some(NameId(2))` on top-level commas and `: `.
fn split_fields(body: &str) -> Vec<(String, String)> {
    let mut fields = Vec::new();
    let mut depth = 0i32;
    let mut current = String::new();
    for character in body.chars() {
        match character {
            '(' | '[' | '{' => depth += 1,
            ')' | ']' | '}' => depth -= 1,
            ',' if depth == 0 => {
                push_field(&mut fields, &current);
                current.clear();
                continue;
            }
            _ => {}
        }
        current.push(character);
    }
    push_field(&mut fields, &current);
    fields
}

/// Pushes one `key: value` chunk, ignoring an empty tail.
fn push_field(fields: &mut Vec<(String, String)>, chunk: &str) {
    let chunk = chunk.trim();
    if chunk.is_empty() {
        return;
    }
    match chunk.split_once(": ") {
        Some((key, value)) => fields.push((key.trim().to_owned(), value.trim().to_owned())),
        None => fields.push((chunk.to_owned(), String::new())),
    }
}

/// `{name table index -> rendered declaration name}` for everything in the
/// environment.
///
/// A `NameId` cannot be rebuilt from its raw index outside the kernel crate, so
/// this is how a `Debug`-rendered `NameId(7)` in an error payload is turned back
/// into `Nat.add_comm`. Only names that are *declared* resolve; anything else is
/// left as the raw handle rather than guessed at.
fn environment_name_index(kernel: &Kernel) -> HashMap<usize, String> {
    kernel
        .environment()
        .iter()
        .map(|(id, _)| (id.index(), kernel.display_name(*id).to_string()))
        .collect()
}

/// The declaration name a `NameId(7)`-shaped payload refers to, if it is one.
fn resolve_debug_name(index: &HashMap<usize, String>, value: &str) -> Option<String> {
    let inner = value
        .strip_prefix("NameId(")
        .or_else(|| value.strip_prefix("Some(NameId("))?;
    let digits: String = inner.chars().take_while(char::is_ascii_digit).collect();
    index.get(&digits.parse::<usize>().ok()?).cloned()
}

// ---------------------------------------------------------------------------
// The kernel
// ---------------------------------------------------------------------------

/// An independent Lean kernel: term language, environment, type checker.
///
/// Every constructor interns (`&mut self` in Rust) and every query reads
/// (`&self`), so Python gets a real reader/writer discipline: a `Kernel` cannot
/// be mutated while a query is in flight.
///
/// Handles this kernel returns are stamped with its `epoch` and refused by any
/// other kernel — see the module docstring.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyclass(module = "axeyum._native.kernel")
)]
#[pyclass(module = "axeyum", name = "Kernel")]
pub struct PyKernel {
    /// The wrapped kernel.
    inner: Kernel,
    /// This kernel's handle epoch.
    epoch: u64,
}

impl PyKernel {
    /// Wraps an already-checked `Kernel` under a **fresh** epoch.
    ///
    /// Used by `crate::producers` for the kernel an NDJSON statement import
    /// publishes. The epoch is new because the handles that kernel's own
    /// import minted (`goal`, `target_name`) are re-stamped with it at the
    /// same moment, so nothing outside this crate ever sees an unstamped one.
    pub(crate) fn from_kernel(inner: Kernel) -> Self {
        Self {
            inner,
            epoch: next_epoch(),
        }
    }

    /// This kernel's handle epoch.
    pub(crate) fn epoch_value(&self) -> u64 {
        self.epoch
    }

    /// The wrapped kernel, for a read-only Rust call.
    pub(crate) fn inner(&self) -> &Kernel {
        &self.inner
    }

    /// The wrapped kernel, for a Rust call that interns or admits.
    pub(crate) fn inner_mut(&mut self) -> &mut Kernel {
        &mut self.inner
    }

    /// Validates and unwraps a name handle.
    pub(crate) fn name_of(&self, handle: PyNameId) -> PyResult<NameId> {
        epoch_guard(self.epoch, handle.epoch, "NameId")?;
        Ok(handle.id)
    }

    /// Validates and unwraps a level handle.
    fn level_of(&self, handle: PyLevelId) -> PyResult<LevelId> {
        epoch_guard(self.epoch, handle.epoch, "LevelId")?;
        Ok(handle.id)
    }

    /// Validates and unwraps an expression handle.
    pub(crate) fn expr_of(&self, handle: PyExprId) -> PyResult<ExprId> {
        epoch_guard(self.epoch, handle.epoch, "ExprId")?;
        Ok(handle.id)
    }

    /// Validates and unwraps a list of name handles.
    fn names_of(&self, handles: &[PyNameId]) -> PyResult<Vec<NameId>> {
        handles.iter().map(|h| self.name_of(*h)).collect()
    }

    /// Validates and unwraps a list of level handles.
    fn levels_of(&self, handles: &[PyLevelId]) -> PyResult<Vec<LevelId>> {
        handles.iter().map(|h| self.level_of(*h)).collect()
    }

    /// Stamps a name handle with this kernel's epoch.
    pub(crate) fn wrap_name(&self, id: NameId) -> PyNameId {
        PyNameId {
            epoch: self.epoch,
            id,
        }
    }

    /// Stamps a level handle with this kernel's epoch.
    fn wrap_level(&self, id: LevelId) -> PyLevelId {
        PyLevelId {
            epoch: self.epoch,
            id,
        }
    }

    /// Stamps an expression handle with this kernel's epoch.
    pub(crate) fn wrap_expr(&self, id: ExprId) -> PyExprId {
        PyExprId {
            epoch: self.epoch,
            id,
        }
    }

    /// Interns a dotted declaration name, component by component.
    ///
    /// Promoted from `examples/autogenesis_support::intern_dotted`, which every
    /// example needed and no library exposed.
    fn intern_dotted(&mut self, rendered: &str) -> PyResult<NameId> {
        if rendered.is_empty() || rendered.split('.').any(str::is_empty) {
            return Err(PyValueError::new_err(format!(
                "invalid dotted declaration name {rendered:?}"
            )));
        }
        let mut name = self.inner.anon();
        for component in rendered.split('.') {
            name = self.inner.name_str(name, component);
        }
        Ok(name)
    }

    /// Resolves a `NameId` handle or a dotted string to an interned name.
    fn resolve(&mut self, name: &Bound<'_, PyAny>) -> PyResult<NameId> {
        if let Ok(handle) = name.extract::<PyNameId>() {
            return self.name_of(handle);
        }
        if let Ok(text) = name.extract::<String>() {
            return self.intern_dotted(&text);
        }
        Err(PyTypeError::new_err(
            "expected a NameId or a dotted name string such as \"Nat.add_comm\"",
        ))
    }

    /// Resolves a name and requires that it names a declaration.
    ///
    /// This is principle 4 made mechanical: `axiom_footprint` on an **absent**
    /// name returns `[]`, byte-identical to the answer for an axiom-free
    /// theorem. Letting that through would let a typo read as this project's
    /// headline claim.
    fn require_declaration(&mut self, name: &Bound<'_, PyAny>) -> PyResult<NameId> {
        let id = self.resolve(name)?;
        if self.inner.environment().contains(id) {
            return Ok(id);
        }
        Err(PyKeyError::new_err(format!(
            "no declaration named {} in this kernel ({} declarations). An absent name is a \
             FAILED lookup here, not an empty footprint.",
            self.inner.display_name(id),
            self.inner.environment().len()
        )))
    }

    /// Projects a Rust `KernelError` onto the Python `KernelError` exception.
    fn kernel_error(&self, py: Python<'_>, error: &RustKernelError) -> PyErr {
        let debug = format!("{error:?}");
        let (variant, fields) = split_debug(&debug);
        let raised = KernelError::new_err(format!("{variant}: {debug}"));
        let value = raised.value(py);
        let index = environment_name_index(&self.inner);
        let payload = PyDict::new(py);
        let names = PyDict::new(py);
        for (key, rendered) in &fields {
            if payload.set_item(key, rendered).is_err() {
                return raised;
            }
            if let Some(resolved) = resolve_debug_name(&index, rendered)
                && names.set_item(key, resolved).is_err()
            {
                return raised;
            }
        }
        if value.setattr("variant", &variant).is_err()
            || value.setattr("fields", payload).is_err()
            || value.setattr("names", names).is_err()
            || value.setattr("debug", &debug).is_err()
        {
            return raised;
        }
        raised
    }

    /// Copies one expression node out of the arena.
    fn node_of(&self, id: ExprId) -> PyExprNode {
        match self.inner.expr_node(id) {
            ExprNode::BVar(index) => {
                let mut node = PyExprNode::blank("bvar");
                node.index = Some(*index);
                node
            }
            ExprNode::FVar(fvar) => {
                let mut node = PyExprNode::blank("fvar");
                node.fvar_id = Some(*fvar);
                node
            }
            ExprNode::Sort(level) => {
                let mut node = PyExprNode::blank("sort");
                node.level = Some(self.wrap_level(*level));
                node
            }
            ExprNode::Const(name, levels) => {
                let mut node = PyExprNode::blank("const");
                node.name = Some(self.wrap_name(*name));
                node.levels = Some(levels.iter().map(|&l| self.wrap_level(l)).collect());
                node
            }
            ExprNode::Proj(name, field, structure) => {
                let mut node = PyExprNode::blank("proj");
                node.name = Some(self.wrap_name(*name));
                node.field_index = Some(*field);
                node.structure = Some(self.wrap_expr(*structure));
                node
            }
            ExprNode::App(fun, arg) => {
                let mut node = PyExprNode::blank("app");
                node.fun = Some(self.wrap_expr(*fun));
                node.arg = Some(self.wrap_expr(*arg));
                node
            }
            ExprNode::Lam(name, ty, body, info) => {
                let mut node = PyExprNode::blank("lam");
                node.name = Some(self.wrap_name(*name));
                node.ty = Some(self.wrap_expr(*ty));
                node.body = Some(self.wrap_expr(*body));
                node.binder = Some((*info).into());
                node
            }
            ExprNode::Pi(name, ty, body, info) => {
                let mut node = PyExprNode::blank("pi");
                node.name = Some(self.wrap_name(*name));
                node.ty = Some(self.wrap_expr(*ty));
                node.body = Some(self.wrap_expr(*body));
                node.binder = Some((*info).into());
                node
            }
            ExprNode::Let(name, ty, value, body) => {
                let mut node = PyExprNode::blank("let");
                node.name = Some(self.wrap_name(*name));
                node.ty = Some(self.wrap_expr(*ty));
                node.value = Some(self.wrap_expr(*value));
                node.body = Some(self.wrap_expr(*body));
                node
            }
            ExprNode::Lit(lit) => {
                let mut node = PyExprNode::blank("lit");
                node.lit = Some(PyLit { inner: lit.clone() });
                node
            }
        }
    }
}

/// The stack a `build_*_prelude` recursion is run on.
///
/// The default 8 MB main-thread stack is not enough for the deepest constructed
/// numeric preludes. `cpoint` failed there in the original 2026-08-25 audit;
/// `creal` and `complex` independently reproduced SIGSEGV there on 2026-08-30
/// after their libraries grew. 64 MB is a factor of four above the last size
/// measured to pass, on a thread that lives only for the duration of one call.
const DEEP_STACK_BYTES: usize = 64 * 1024 * 1024;

/// Runs `work` on a thread with [`DEEP_STACK_BYTES`] of stack, turning a panic
/// inside it into an `Err` carrying the panic message.
///
/// Two problems, one mechanism. The stack size is what stops a deeply recursive
/// prelude builder from overflowing -- and a stack overflow is NOT a panic, so
/// `catch_unwind` could not have helped with it at all. `join()` is what turns a
/// panic that does happen into a value, without `catch_unwind` and without
/// widening `unsafe_code`.
///
/// A SCOPED thread is what lets `work` borrow the kernel mutably; a detached
/// `thread::spawn` would demand `'static`.
///
/// # Errors
///
/// Returns the panic message when `work` panicked, or the spawn failure.
fn on_deep_stack<T, F>(work: F) -> Result<T, String>
where
    F: FnOnce() -> T + Send,
    T: Send,
{
    std::thread::scope(|scope| {
        let handle = std::thread::Builder::new()
            .stack_size(DEEP_STACK_BYTES)
            .spawn_scoped(scope, work)
            .map_err(|error| format!("could not start the deep-stack thread: {error}"))?;
        handle.join().map_err(|payload| {
            payload
                .downcast_ref::<&str>()
                .map(|text| (*text).to_owned())
                .or_else(|| payload.downcast_ref::<String>().cloned())
                .unwrap_or_else(|| "panic payload was not a string".to_owned())
        })
    })
}

// PyO3 extracts OWNED values across the FFI edge: a `&[T]` or a `&PyRef<T>`
// cannot be built from a Python object, so every argument below is by value
// whether or not the body consumes it.
#[allow(clippy::needless_pass_by_value)]
#[cfg_attr(feature = "stub-gen", pyo3_stub_gen::derive::gen_stub_pymethods)]
#[pymethods]
impl PyKernel {
    /// A pristine kernel with an empty environment and a fresh epoch.
    #[new]
    fn new() -> Self {
        Self {
            inner: Kernel::new(),
            epoch: next_epoch(),
        }
    }

    /// This kernel's handle epoch.
    #[getter]
    fn epoch(&self) -> u64 {
        self.epoch
    }

    /// A full snapshot of this kernel, under a **new** epoch.
    ///
    /// `Kernel` derives `Clone` over plain owned data, so a fork is a genuine
    /// independent copy — the snapshot primitive this binding has.
    ///
    /// The fork **rejects this kernel's handles**, and that is deliberate. The
    /// two kernels agree on every id at the instant of the fork, so accepting
    /// them would work right up until either side interns something new, after
    /// which the same `ExprId` denotes two different terms and nothing signals
    /// it. A handle is a promise about one arena's future, and a fork does not
    /// inherit that promise. Re-resolve names by string across a fork.
    fn fork(&self) -> Self {
        Self {
            inner: self.inner.clone(),
            epoch: next_epoch(),
        }
    }

    // -- preludes ----------------------------------------------------------

    /// Builds the logic prelude (`Eq`, `And`, `Or`, decidability, …).
    ///
    /// # Errors
    ///
    /// Raises `KernelError` if the kernel refuses any declaration in the
    /// package.
    fn build_logic_prelude(&mut self, py: Python<'_>) -> PyResult<Py<PyPrelude>> {
        let kernel = &mut self.inner;
        let built = py.detach(move || build_logic_prelude(kernel));
        let package = built.map_err(|error| self.kernel_error(py, &error))?;
        make_prelude(
            py,
            self.epoch,
            "logic",
            prelude_fields::logic(&package),
            Vec::new(),
            Some(Box::new(package)),
        )
    }

    /// Builds the computational `Nat` prelude.
    ///
    /// # Errors
    ///
    /// Raises `KernelError` if the kernel refuses any declaration in the
    /// package.
    fn build_nat_prelude(&mut self, py: Python<'_>) -> PyResult<Py<PyPrelude>> {
        let kernel = &mut self.inner;
        let built = py.detach(move || build_nat_prelude(kernel));
        let package = built.map_err(|error| self.kernel_error(py, &error))?;
        make_prelude(
            py,
            self.epoch,
            "nat",
            prelude_fields::nat(&package),
            prelude_fields::nat_sub(&package),
            None,
        )
    }

    /// Builds the `Int` prelude.
    ///
    /// # Errors
    ///
    /// Raises `KernelError` if the kernel refuses any declaration in the
    /// package.
    fn build_int_prelude(&mut self, py: Python<'_>) -> PyResult<Py<PyPrelude>> {
        let kernel = &mut self.inner;
        let built = py.detach(move || build_int_prelude(kernel));
        let package = built.map_err(|error| self.kernel_error(py, &error))?;
        make_prelude(
            py,
            self.epoch,
            "int",
            prelude_fields::int(&package),
            prelude_fields::int_sub(&package),
            None,
        )
    }

    /// Builds the `Rat` prelude.
    ///
    /// # Errors
    ///
    /// Raises `KernelError` if the kernel refuses any declaration in the
    /// package.
    fn build_rat_prelude(&mut self, py: Python<'_>) -> PyResult<Py<PyPrelude>> {
        let kernel = &mut self.inner;
        let built = py.detach(move || build_rat_prelude(kernel));
        let package = built.map_err(|error| self.kernel_error(py, &error))?;
        make_prelude(
            py,
            self.epoch,
            "rat",
            prelude_fields::rat(&package),
            prelude_fields::rat_sub(&package),
            None,
        )
    }

    /// Builds the **axiomatized** ordered field `AxReal` (prelude key
    /// `axreal`).
    ///
    /// This is the repository's only nonzero axiom row: **30 declared axioms**,
    /// and 30 is a floor rather than a dial — `AxReal`'s carrier is opaque, so
    /// nothing over it is definable and every operation and law must be
    /// assumed. **No shipped route reaches them**: `Lra`, `DisjunctiveLra`,
    /// `Sos` and `IntFarkas` all reconstruct over constructed carriers. Quote
    /// the pair — "30 declared, none reached" — because "we have 30 axioms"
    /// ignores the second half and "our proofs rest on 30 axioms" is false.
    ///
    /// For the constructed reals, which measure 0, use
    /// [`Self::build_creal_prelude`].
    ///
    /// # Errors
    ///
    /// Raises `KernelError` if the kernel refuses any declaration in the
    /// package.
    fn build_arith_prelude(&mut self, py: Python<'_>) -> PyResult<Py<PyPrelude>> {
        let kernel = &mut self.inner;
        let built = py.detach(move || build_arith_prelude(kernel));
        let package = built.map_err(|error| self.kernel_error(py, &error))?;
        make_prelude(
            py,
            self.epoch,
            "axreal",
            prelude_fields::arith(&package),
            prelude_fields::arith_sub(&package),
            None,
        )
    }

    /// Builds the **constructed** reals `CReal` — a Bishop setoid over the
    /// constructed rationals, trusted surface 0 (ADR-0512).
    ///
    /// `CReal` and `AxReal` are different things and one is a substring of the
    /// other: a `"Real."` test matches `"CReal."`. Decide which package you mean
    /// by its declaration, never by a substring.
    ///
    /// This is the expensive one — a debug build was measured at **44 s**
    /// against `AxReal`'s 5.6 ms — which is what the process-wide prelude cache
    /// exists for. The call releases the GIL.
    ///
    /// # Errors
    ///
    /// Raises `KernelError` if the kernel refuses any declaration in the
    /// package.
    fn build_creal_prelude(&mut self, py: Python<'_>) -> PyResult<Py<PyPrelude>> {
        let kernel = &mut self.inner;
        let built = py.detach(move || on_deep_stack(move || build_creal_prelude(kernel)));
        let built = built.map_err(|detail| {
            InternalError::new_err(format!(
                "axeyum_lean_kernel::build_creal_prelude panicked: {detail}"
            ))
        })?;
        let package = built.map_err(|error| self.kernel_error(py, &error))?;
        make_prelude(
            py,
            self.epoch,
            "creal",
            prelude_fields::creal(&package),
            prelude_fields::creal_sub(&package),
            None,
        )
    }

    /// Builds the complex-number prelude over the constructed reals.
    ///
    /// # Errors
    ///
    /// Raises `KernelError` if the kernel refuses any declaration in the
    /// package.
    fn build_complex_prelude(&mut self, py: Python<'_>) -> PyResult<Py<PyPrelude>> {
        let kernel = &mut self.inner;
        let built = py.detach(move || on_deep_stack(move || build_complex_prelude(kernel)));
        let built = built.map_err(|detail| {
            InternalError::new_err(format!(
                "axeyum_lean_kernel::build_complex_prelude panicked: {detail}"
            ))
        })?;
        let package = built.map_err(|error| self.kernel_error(py, &error))?;
        make_prelude(
            py,
            self.epoch,
            "complex",
            prelude_fields::complex(&package),
            prelude_fields::complex_sub(&package),
            None,
        )
    }

    /// Builds the constructed-real plane-geometry prelude.
    ///
    /// # Errors
    ///
    /// Raises `KernelError` if the kernel refuses any declaration in the
    /// package.
    fn build_cpoint_prelude(&mut self, py: Python<'_>) -> PyResult<Py<PyPrelude>> {
        let kernel = &mut self.inner;
        // ON A DEEP STACK, and this one is not optional. Measured 2026-08-25:
        // `Kernel().build_cpoint_prelude()` on the 8 MB main-thread stack kills
        // CPython with SIGSEGV -- silently, no traceback, no `PanicException`,
        // nothing an `except` of any kind can see -- while the same call on a
        // 16 MB stack returns a 106-name prelude. CReal and Complex now use the
        // same boundary because they also outgrew the default stack.
        //
        // NO PREFLIGHT IS POSSIBLE HERE. The input is the empty kernel: there is
        // no argument to screen and no caller mistake to report, so the only fix
        // is to give the recursion the room it needs.
        let built = py.detach(move || on_deep_stack(move || build_cpoint_prelude(kernel)));
        let built = built.map_err(|detail| {
            InternalError::new_err(format!(
                "axeyum_lean_kernel::build_cpoint_prelude panicked: {detail}"
            ))
        })?;
        let package = built.map_err(|error| self.kernel_error(py, &error))?;
        make_prelude(
            py,
            self.epoch,
            "cpoint",
            prelude_fields::cpoint(&package),
            prelude_fields::cpoint_sub(&package),
            None,
        )
    }

    /// Builds the string prelude over `num_chars` characters.
    ///
    /// This is the one builder that takes a caller-held package: it needs the
    /// exact `LogicPrelude` this kernel was built with, so it can never start
    /// from a pristine kernel and deliberately has no template in the process
    /// cache. Pass the object returned by [`Self::build_logic_prelude`].
    ///
    /// `num_chars` is the alphabet size and is **required**: it selects the
    /// `axeyum.string.<size>` namespace, so a default here would silently pick
    /// which string theory you get.
    ///
    /// # Errors
    ///
    /// Raises `EpochError` if `logic` came from another kernel, `ValueError` if
    /// it is not a logic package, and `KernelError` if the kernel refuses the
    /// build (including a `PreludePackageConflict` when `logic` is not the
    /// package this kernel holds).
    fn build_string_prelude(
        &mut self,
        py: Python<'_>,
        logic: PyRef<'_, PyPrelude>,
        num_chars: usize,
    ) -> PyResult<Py<PyPrelude>> {
        epoch_guard(self.epoch, logic.epoch, "Prelude")?;
        let package = logic.logic.as_deref().copied().ok_or_else(|| {
            PyValueError::new_err(format!(
                "build_string_prelude needs the logic package returned by \
                 build_logic_prelude, got a {:?} package",
                logic.kind
            ))
        })?;
        drop(logic);
        let kernel = &mut self.inner;
        let built = py.detach(move || build_string_prelude(kernel, package, num_chars));
        let built = built.map_err(|error| self.kernel_error(py, &error))?;
        make_prelude(
            py,
            self.epoch,
            "string",
            prelude_fields::string(&built),
            prelude_fields::string_sub(&built),
            None,
        )
    }

    // -- names -------------------------------------------------------------

    /// The anonymous root name every dotted name is built on.
    fn anon(&mut self) -> PyNameId {
        let id = self.inner.anon();
        self.wrap_name(id)
    }

    /// Appends a string component to `parent`.
    ///
    /// # Errors
    ///
    /// Raises `EpochError` if `parent` came from another kernel.
    fn name_str(&mut self, parent: PyNameId, component: String) -> PyResult<PyNameId> {
        let parent = self.name_of(parent)?;
        let id = self.inner.name_str(parent, component);
        Ok(self.wrap_name(id))
    }

    /// Appends a numeric component to `parent`.
    ///
    /// # Errors
    ///
    /// Raises `EpochError` if `parent` came from another kernel.
    fn name_num(&mut self, parent: PyNameId, component: u64) -> PyResult<PyNameId> {
        let parent = self.name_of(parent)?;
        let id = self.inner.name_num(parent, component);
        Ok(self.wrap_name(id))
    }

    /// Interns a dotted name such as `"Nat.add_comm"`.
    ///
    /// With `must_exist=True` the name must already denote a declaration in this
    /// kernel; interning succeeds for any well-formed dotted string otherwise,
    /// because building a *new* declaration needs a name before the declaration
    /// exists.
    ///
    /// # Errors
    ///
    /// Raises `ValueError` for a malformed dotted string and `KeyError` when
    /// `must_exist=True` and nothing is declared under that name.
    #[pyo3(signature = (dotted, *, must_exist = false))]
    fn name(&mut self, dotted: &str, must_exist: bool) -> PyResult<PyNameId> {
        let id = self.intern_dotted(dotted)?;
        if must_exist && !self.inner.environment().contains(id) {
            return Err(PyKeyError::new_err(format!(
                "no declaration named {dotted:?} in this kernel ({} declarations)",
                self.inner.environment().len()
            )));
        }
        Ok(self.wrap_name(id))
    }

    /// The dotted rendering of a name (`a.b.1`; the anonymous root prints as
    /// `[anonymous]`).
    ///
    /// This is what the kernel's own inventories print. It is **not** what a
    /// generated Lean module spells — see [`Self::lean_name`].
    ///
    /// # Errors
    ///
    /// Raises `EpochError` if the handle came from another kernel.
    fn display_name(&self, name: PyNameId) -> PyResult<String> {
        let id = self.name_of(name)?;
        Ok(self.inner.display_name(id).to_string())
    }

    /// The name as an **emitted Lean module** spells it.
    ///
    /// Two rules diverge from [`Self::display_name`], and both bite anything
    /// matching a footprint against `axiom` lines in a module: a numeric
    /// component is not a legal Lean identifier, so `x.0` is emitted `x._0`;
    /// and the kernel's computational naturals are rooted at `AxNat` so they do
    /// not shadow Lean's `Nat`.
    ///
    /// # Errors
    ///
    /// Raises `EpochError` if the handle came from another kernel.
    fn lean_name(&self, name: PyNameId) -> PyResult<String> {
        let id = self.name_of(name)?;
        Ok(self.inner.lean_name(id))
    }

    /// The structural node of a name: `("anonymous",)`, `("str", parent, s)`,
    /// or `("num", parent, n)`.
    ///
    /// # Errors
    ///
    /// Raises `EpochError` if the handle came from another kernel, and
    /// propagates any Python error raised while building the tuple.
    fn name_node<'py>(&self, py: Python<'py>, name: PyNameId) -> PyResult<Bound<'py, PyTuple>> {
        let id = self.name_of(name)?;
        let tuple = match self.inner.name_node(id) {
            NameNode::Anonymous => ("anonymous",).into_pyobject(py)?.into_any(),
            NameNode::Str(parent, component) => ("str", self.wrap_name(*parent), component.clone())
                .into_pyobject(py)?
                .into_any(),
            NameNode::Num(parent, component) => ("num", self.wrap_name(*parent), *component)
                .into_pyobject(py)?
                .into_any(),
        };
        tuple.cast_into::<PyTuple>().map_err(Into::into)
    }

    // -- levels ------------------------------------------------------------

    /// The universe level `0` (`Prop`'s level).
    fn level_zero(&mut self) -> PyLevelId {
        let id = self.inner.level_zero();
        self.wrap_level(id)
    }

    /// One level above `level`.
    ///
    /// # Errors
    ///
    /// Raises `EpochError` if the handle came from another kernel.
    fn level_succ(&mut self, level: PyLevelId) -> PyResult<PyLevelId> {
        let id = self.level_of(level)?;
        let succ = self.inner.level_succ(id);
        Ok(self.wrap_level(succ))
    }

    /// The larger of two levels.
    ///
    /// # Errors
    ///
    /// Raises `EpochError` if a handle came from another kernel.
    fn level_max(&mut self, left: PyLevelId, right: PyLevelId) -> PyResult<PyLevelId> {
        let left = self.level_of(left)?;
        let right = self.level_of(right)?;
        let id = self.inner.level_max(left, right);
        Ok(self.wrap_level(id))
    }

    /// The impredicative max: `0` when `right` is `0`, else `max`.
    ///
    /// # Errors
    ///
    /// Raises `EpochError` if a handle came from another kernel.
    fn level_imax(&mut self, left: PyLevelId, right: PyLevelId) -> PyResult<PyLevelId> {
        let left = self.level_of(left)?;
        let right = self.level_of(right)?;
        let id = self.inner.level_imax(left, right);
        Ok(self.wrap_level(id))
    }

    /// A universe parameter (variable) named `name`.
    ///
    /// # Errors
    ///
    /// Raises `EpochError` if the handle came from another kernel.
    fn level_param(&mut self, name: PyNameId) -> PyResult<PyLevelId> {
        let id = self.name_of(name)?;
        let level = self.inner.level_param(id);
        Ok(self.wrap_level(level))
    }

    /// `level + offset`, as `offset` nested `succ`s.
    ///
    /// # Errors
    ///
    /// Raises `EpochError` if the handle came from another kernel.
    fn level_offset(&mut self, level: PyLevelId, offset: u64) -> PyResult<PyLevelId> {
        let id = self.level_of(level)?;
        let offset = self.inner.level_offset(id, offset);
        Ok(self.wrap_level(offset))
    }

    /// Splits a `succ` chain into `(base, height)`.
    ///
    /// # Errors
    ///
    /// Raises `EpochError` if the handle came from another kernel.
    fn level_succs(&self, level: PyLevelId) -> PyResult<(PyLevelId, usize)> {
        let id = self.level_of(level)?;
        let (base, height) = self.inner.level_succs(id);
        Ok((self.wrap_level(base), height))
    }

    /// The normal form of a level.
    ///
    /// Named `simplify_level`, not `simplify`: a bare `simplify` on a kernel
    /// reads as term simplification, which this is not.
    ///
    /// # Errors
    ///
    /// Raises `EpochError` if the handle came from another kernel.
    fn simplify_level(&mut self, level: PyLevelId) -> PyResult<PyLevelId> {
        let id = self.level_of(level)?;
        let simplified = self.inner.simplify(id);
        Ok(self.wrap_level(simplified))
    }

    /// Whether `left <= right` holds for every universe assignment.
    ///
    /// # Errors
    ///
    /// Raises `EpochError` if a handle came from another kernel.
    fn level_leq(&mut self, left: PyLevelId, right: PyLevelId) -> PyResult<bool> {
        let left = self.level_of(left)?;
        let right = self.level_of(right)?;
        Ok(self.inner.level_leq(left, right))
    }

    /// Whether two levels are equivalent for every universe assignment.
    ///
    /// # Errors
    ///
    /// Raises `EpochError` if a handle came from another kernel.
    fn level_is_equiv(&mut self, left: PyLevelId, right: PyLevelId) -> PyResult<bool> {
        let left = self.level_of(left)?;
        let right = self.level_of(right)?;
        Ok(self.inner.level_is_equiv(left, right))
    }

    /// Whether the level is definitely `0`.
    ///
    /// # Errors
    ///
    /// Raises `EpochError` if the handle came from another kernel.
    fn level_is_zero(&mut self, level: PyLevelId) -> PyResult<bool> {
        let id = self.level_of(level)?;
        Ok(self.inner.level_is_zero(id))
    }

    /// Whether the level is definitely nonzero.
    ///
    /// # Errors
    ///
    /// Raises `EpochError` if the handle came from another kernel.
    fn level_is_nonzero(&mut self, level: PyLevelId) -> PyResult<bool> {
        let id = self.level_of(level)?;
        Ok(self.inner.level_is_nonzero(id))
    }

    /// Substitutes universe parameters in a level.
    ///
    /// # Errors
    ///
    /// Raises `EpochError` if a handle came from another kernel.
    fn substitute_level(
        &mut self,
        level: PyLevelId,
        subst: Vec<(PyNameId, PyLevelId)>,
    ) -> PyResult<PyLevelId> {
        let id = self.level_of(level)?;
        let pairs = subst
            .into_iter()
            .map(|(name, value)| Ok((self.name_of(name)?, self.level_of(value)?)))
            .collect::<PyResult<Vec<_>>>()?;
        let substituted = self.inner.substitute_level(id, &pairs);
        Ok(self.wrap_level(substituted))
    }

    /// Substitutes universe parameters throughout an expression.
    ///
    /// # Errors
    ///
    /// Raises `EpochError` if a handle came from another kernel.
    fn substitute_expr_levels(
        &mut self,
        expr: PyExprId,
        subst: Vec<(PyNameId, PyLevelId)>,
    ) -> PyResult<PyExprId> {
        let id = self.expr_of(expr)?;
        let pairs = subst
            .into_iter()
            .map(|(name, value)| Ok((self.name_of(name)?, self.level_of(value)?)))
            .collect::<PyResult<Vec<_>>>()?;
        let substituted = self.inner.substitute_expr_levels(id, &pairs);
        Ok(self.wrap_expr(substituted))
    }

    // -- expressions -------------------------------------------------------

    /// A bound variable by de Bruijn index (0 = innermost binder).
    fn bvar(&mut self, index: u32) -> PyExprId {
        let id = self.inner.bvar(index);
        self.wrap_expr(id)
    }

    /// A free/local variable by unique id.
    fn fvar(&mut self, id: u64) -> PyExprId {
        let expr = self.inner.fvar(id);
        self.wrap_expr(expr)
    }

    /// The type universe at `level`.
    ///
    /// # Errors
    ///
    /// Raises `EpochError` if the handle came from another kernel.
    fn sort(&mut self, level: PyLevelId) -> PyResult<PyExprId> {
        let id = self.level_of(level)?;
        let expr = self.inner.sort(id);
        Ok(self.wrap_expr(expr))
    }

    /// `Sort 0`, i.e. `Prop`.
    fn sort_zero(&mut self) -> PyExprId {
        let id = self.inner.sort_zero();
        self.wrap_expr(id)
    }

    /// A constant reference with universe arguments.
    ///
    /// Named `const_` because `const` is not a Python identifier hazard but is a
    /// Rust keyword; the Rust method is `const_` too.
    ///
    /// # Errors
    ///
    /// Raises `EpochError` if a handle came from another kernel.
    fn const_(&mut self, name: PyNameId, levels: Vec<PyLevelId>) -> PyResult<PyExprId> {
        let name = self.name_of(name)?;
        let levels = self.levels_of(&levels)?;
        let expr = self.inner.const_(name, levels);
        Ok(self.wrap_expr(expr))
    }

    /// A structure projection by zero-based field index (parameters excluded).
    ///
    /// # Errors
    ///
    /// Raises `EpochError` if a handle came from another kernel.
    fn proj(
        &mut self,
        type_name: PyNameId,
        field_index: u32,
        structure: PyExprId,
    ) -> PyResult<PyExprId> {
        let type_name = self.name_of(type_name)?;
        let structure = self.expr_of(structure)?;
        let expr = self.inner.proj(type_name, field_index, structure);
        Ok(self.wrap_expr(expr))
    }

    /// Function application `fun arg`.
    ///
    /// # Errors
    ///
    /// Raises `EpochError` if a handle came from another kernel.
    fn app(&mut self, fun: PyExprId, arg: PyExprId) -> PyResult<PyExprId> {
        let fun = self.expr_of(fun)?;
        let arg = self.expr_of(arg)?;
        let expr = self.inner.app(fun, arg);
        Ok(self.wrap_expr(expr))
    }

    /// `fun (name : ty) => body`.
    ///
    /// # Errors
    ///
    /// Raises `EpochError` if a handle came from another kernel.
    #[pyo3(signature = (name, ty, body, info = PyBinderInfo::Default))]
    fn lam(
        &mut self,
        name: PyNameId,
        ty: PyExprId,
        body: PyExprId,
        info: PyBinderInfo,
    ) -> PyResult<PyExprId> {
        let name = self.name_of(name)?;
        let ty = self.expr_of(ty)?;
        let body = self.expr_of(body)?;
        let expr = self.inner.lam(name, ty, body, info.into());
        Ok(self.wrap_expr(expr))
    }

    /// `(name : ty) -> body`, the dependent function type.
    ///
    /// # Errors
    ///
    /// Raises `EpochError` if a handle came from another kernel.
    #[pyo3(signature = (name, ty, body, info = PyBinderInfo::Default))]
    fn pi(
        &mut self,
        name: PyNameId,
        ty: PyExprId,
        body: PyExprId,
        info: PyBinderInfo,
    ) -> PyResult<PyExprId> {
        let name = self.name_of(name)?;
        let ty = self.expr_of(ty)?;
        let body = self.expr_of(body)?;
        let expr = self.inner.pi(name, ty, body, info.into());
        Ok(self.wrap_expr(expr))
    }

    /// `let name : ty := value; body`.
    ///
    /// # Errors
    ///
    /// Raises `EpochError` if a handle came from another kernel.
    fn let_(
        &mut self,
        name: PyNameId,
        ty: PyExprId,
        value: PyExprId,
        body: PyExprId,
    ) -> PyResult<PyExprId> {
        let name = self.name_of(name)?;
        let ty = self.expr_of(ty)?;
        let value = self.expr_of(value)?;
        let body = self.expr_of(body)?;
        let expr = self.inner.let_(name, ty, value, body);
        Ok(self.wrap_expr(expr))
    }

    /// A literal expression.
    fn lit(&mut self, lit: PyLit) -> PyExprId {
        let expr = self.inner.lit(lit.inner);
        self.wrap_expr(expr)
    }

    /// The destructured node of an expression, copied out of the arena.
    ///
    /// # Errors
    ///
    /// Raises `EpochError` if the handle came from another kernel.
    fn expr_node(&self, expr: PyExprId) -> PyResult<PyExprNode> {
        let id = self.expr_of(expr)?;
        Ok(self.node_of(id))
    }

    /// A lambda's body, or `None` if the expression is not a lambda.
    ///
    /// # Errors
    ///
    /// Raises `EpochError` if the handle came from another kernel.
    fn lam_body(&self, expr: PyExprId) -> PyResult<Option<PyExprId>> {
        let id = self.expr_of(expr)?;
        Ok(self.inner.lam_body(id).map(|body| self.wrap_expr(body)))
    }

    /// A pi's body, or `None` if the expression is not a pi.
    ///
    /// # Errors
    ///
    /// Raises `EpochError` if the handle came from another kernel.
    fn pi_body(&self, expr: PyExprId) -> PyResult<Option<PyExprId>> {
        let id = self.expr_of(expr)?;
        Ok(self.inner.pi_body(id).map(|body| self.wrap_expr(body)))
    }

    /// One more than the largest loose de Bruijn index escaping the expression.
    ///
    /// # Errors
    ///
    /// Raises `EpochError` if the handle came from another kernel.
    fn num_loose_bvars(&self, expr: PyExprId) -> PyResult<u32> {
        let id = self.expr_of(expr)?;
        Ok(self.inner.num_loose_bvars(id))
    }

    /// Whether any loose de Bruijn variable escapes the expression.
    ///
    /// # Errors
    ///
    /// Raises `EpochError` if the handle came from another kernel.
    fn has_loose_bvars(&self, expr: PyExprId) -> PyResult<bool> {
        let id = self.expr_of(expr)?;
        Ok(self.inner.has_loose_bvars(id))
    }

    /// The half-open range of loose de Bruijn indices, as `(start, end)`.
    ///
    /// # Errors
    ///
    /// Raises `EpochError` if the handle came from another kernel.
    fn loose_bvar_range(&self, expr: PyExprId) -> PyResult<(u32, u32)> {
        let id = self.expr_of(expr)?;
        let range = self.inner.loose_bvar_range(id);
        Ok((range.start, range.end))
    }

    /// Whether any free variable occurs in the expression.
    ///
    /// # Errors
    ///
    /// Raises `EpochError` if the handle came from another kernel.
    fn has_fvars(&self, expr: PyExprId) -> PyResult<bool> {
        let id = self.expr_of(expr)?;
        Ok(self.inner.has_fvars(id))
    }

    /// Instantiates the outermost loose de Bruijn variables with `subst`.
    ///
    /// # Errors
    ///
    /// Raises `EpochError` if a handle came from another kernel.
    fn instantiate(&mut self, expr: PyExprId, subst: Vec<PyExprId>) -> PyResult<PyExprId> {
        let id = self.expr_of(expr)?;
        let subst = subst
            .iter()
            .map(|e| self.expr_of(*e))
            .collect::<PyResult<Vec<_>>>()?;
        let instantiated = self.inner.instantiate(id, &subst);
        Ok(self.wrap_expr(instantiated))
    }

    /// Abstracts the listed free variables into de Bruijn binders.
    ///
    /// # Errors
    ///
    /// Raises `EpochError` if the handle came from another kernel.
    fn abstract_fvars(&mut self, expr: PyExprId, fvars: Vec<u64>) -> PyResult<PyExprId> {
        let id = self.expr_of(expr)?;
        let abstracted = self.inner.abstract_fvars(id, &fvars);
        Ok(self.wrap_expr(abstracted))
    }

    /// Closes marked `(lambda, fvar)` binder scopes in one traversal.
    ///
    /// # Errors
    ///
    /// Raises `EpochError` if a handle came from another kernel.
    fn close_scoped_fvars(
        &mut self,
        expr: PyExprId,
        binders: Vec<(PyExprId, u64)>,
    ) -> PyResult<PyExprId> {
        let id = self.expr_of(expr)?;
        let binders = binders
            .into_iter()
            .map(|(lambda, fvar)| Ok((self.expr_of(lambda)?, fvar)))
            .collect::<PyResult<Vec<_>>>()?;
        let closed = self.inner.close_scoped_fvars(id, &binders);
        Ok(self.wrap_expr(closed))
    }

    /// Lifts loose de Bruijn variables at or above `cutoff` by `amount`.
    ///
    /// # Errors
    ///
    /// Raises `EpochError` if the handle came from another kernel.
    fn lift_loose_bvars(&mut self, expr: PyExprId, cutoff: u32, amount: u32) -> PyResult<PyExprId> {
        let id = self.expr_of(expr)?;
        let lifted = self.inner.lift_loose_bvars(id, cutoff, amount);
        Ok(self.wrap_expr(lifted))
    }

    // -- checking ----------------------------------------------------------

    /// Infers the type of an expression.
    ///
    /// # Errors
    ///
    /// Raises `EpochError` if the handle came from another kernel, and
    /// `KernelError` for any rejection — a non-function applied, a binder domain
    /// that is not a type, a loose `bvar`, an unknown constant, and so on. The
    /// variant is on `.variant`.
    fn infer(&mut self, py: Python<'_>, expr: PyExprId) -> PyResult<PyExprId> {
        let id = self.expr_of(expr)?;
        let kernel = &mut self.inner;
        let inferred = py.detach(move || kernel.infer(id));
        let inferred = inferred.map_err(|error| self.kernel_error(py, &error))?;
        Ok(self.wrap_expr(inferred))
    }

    /// Definitional equality.
    ///
    /// `False` means "this kernel could not identify them", which for a total
    /// decision procedure over a checked environment is a genuine negative; it
    /// is not an error and not an `unknown`.
    ///
    /// # Errors
    ///
    /// Raises `EpochError` if a handle came from another kernel.
    fn def_eq(&mut self, py: Python<'_>, left: PyExprId, right: PyExprId) -> PyResult<bool> {
        let left = self.expr_of(left)?;
        let right = self.expr_of(right)?;
        let kernel = &mut self.inner;
        Ok(py.detach(move || kernel.def_eq(left, right)))
    }

    /// Weak-head normal form.
    ///
    /// # Errors
    ///
    /// Raises `EpochError` if the handle came from another kernel.
    fn whnf(&mut self, py: Python<'_>, expr: PyExprId) -> PyResult<PyExprId> {
        let id = self.expr_of(expr)?;
        let kernel = &mut self.inner;
        let reduced = py.detach(move || kernel.whnf(id));
        Ok(self.wrap_expr(reduced))
    }

    /// Admits one declaration — **the trusted gate**.
    ///
    /// Every check is genuine and none is skipped: a wrong answer here admits a
    /// false theorem. The call releases the GIL.
    ///
    /// `Declaration.quotient` is deliberately not constructible: the quotient
    /// package is admitted atomically as four declarations, not one at a time.
    ///
    /// # Errors
    ///
    /// Raises `EpochError` if the declaration names another kernel's handles,
    /// and `KernelError` on rejection — `DeclarationExists` for a duplicate
    /// name, `DeclarationValueMismatch` when the value's inferred type is not
    /// the declared one, `UnknownConst` for a dangling reference, and so on.
    fn add_declaration(
        &mut self,
        py: Python<'_>,
        declaration: PyRef<'_, PyDeclaration>,
    ) -> PyResult<()> {
        epoch_guard(self.epoch, declaration.epoch, "Declaration")?;
        let decl = declaration.inner.clone();
        drop(declaration);
        let kernel = &mut self.inner;
        let admitted = py.detach(move || kernel.add_declaration(decl));
        admitted.map_err(|error| self.kernel_error(py, &error))
    }

    /// Admits an inductive type together with its constructors, generating its
    /// recursor and ι-reduction rules.
    ///
    /// # Errors
    ///
    /// Raises `EpochError` if a handle came from another kernel and
    /// `KernelError` on rejection (positivity, malformed constructor type, an
    /// unsupported shape).
    fn add_inductive(
        &mut self,
        py: Python<'_>,
        name: PyNameId,
        uparams: Vec<PyNameId>,
        num_params: usize,
        ty: PyExprId,
        ctors: Vec<(PyNameId, PyExprId)>,
    ) -> PyResult<()> {
        let name = self.name_of(name)?;
        let uparams = self.names_of(&uparams)?;
        let ty = self.expr_of(ty)?;
        let ctors = ctors
            .into_iter()
            .map(|(ctor, ctor_ty)| Ok((self.name_of(ctor)?, self.expr_of(ctor_ty)?)))
            .collect::<PyResult<Vec<_>>>()?;
        let kernel = &mut self.inner;
        let admitted =
            py.detach(move || kernel.add_inductive(name, &uparams, num_params, ty, &ctors));
        admitted.map_err(|error| self.kernel_error(py, &error))
    }

    // -- environment -------------------------------------------------------

    /// An owned snapshot of the environment, `[(rendered name, Declaration)]`,
    /// in the kernel's deterministic id order.
    ///
    /// A snapshot, not a live view: the Rust `environment()` returns a borrow,
    /// and holding one would pin the kernel against the `&mut self` every
    /// constructor needs.
    fn declarations(&self) -> Vec<(String, PyDeclaration)> {
        self.inner
            .environment()
            .iter()
            .map(|(id, declaration)| {
                (
                    self.inner.display_name(*id).to_string(),
                    PyDeclaration {
                        epoch: self.epoch,
                        inner: declaration.clone(),
                    },
                )
            })
            .collect()
    }

    /// Just the declaration NAMES, in environment order.
    ///
    /// [`declarations`](Self::declarations) clones every `Declaration` -- the
    /// whole expression tree of every theorem's type AND proof -- into a Python
    /// object, which for a built prelude is hundreds of them. A caller that only
    /// wants to know what is declared, or to filter before fetching, pays none of
    /// that here -- the `String` per name stays, because a `NameId` renders
    /// through a `Display` wrapper and has no borrowable text -- and then
    /// reaches for
    /// [`get_declaration`](Self::get_declaration) for the ones it wants.
    fn declaration_names(&self) -> Vec<String> {
        self.inner
            .environment()
            .iter()
            .map(|(id, _)| self.inner.display_name(*id).to_string())
            .collect()
    }

    /// The number of declarations in the environment.
    fn declaration_count(&self) -> usize {
        self.inner.environment().len()
    }

    /// Whether `name` (a `NameId` or a dotted string) is declared.
    ///
    /// # Errors
    ///
    /// Raises `EpochError` for a foreign handle, `TypeError` for anything that
    /// is neither a `NameId` nor a string, and `ValueError` for a malformed
    /// dotted name.
    fn contains(&mut self, name: NameLike<'_>) -> PyResult<bool> {
        let id = self.resolve(name.as_any())?;
        Ok(self.inner.environment().contains(id))
    }

    /// The declaration named `name`, or `None`.
    ///
    /// # Errors
    ///
    /// Raises `EpochError` for a foreign handle, `TypeError` for anything that
    /// is neither a `NameId` nor a string, and `ValueError` for a malformed
    /// dotted name.
    fn get_declaration(&mut self, name: NameLike<'_>) -> PyResult<Option<PyDeclaration>> {
        let id = self.resolve(name.as_any())?;
        Ok(self
            .inner
            .environment()
            .get(id)
            .map(|declaration| PyDeclaration {
                epoch: self.epoch,
                inner: declaration.clone(),
            }))
    }

    // -- footprints --------------------------------------------------------

    /// This kernel's `#print axioms`: every trusted declaration `name` rests on,
    /// rendered and sorted.
    ///
    /// An **empty list means axiom-free**, which is a strictly stronger claim
    /// than "we did not find any". That is why an absent name raises `KeyError`
    /// here rather than returning `[]` the way the Rust function does.
    ///
    /// # Errors
    ///
    /// Raises `KeyError` if nothing is declared under `name`.
    fn axiom_footprint(&mut self, name: NameLike<'_>) -> PyResult<Vec<String>> {
        let id = self.require_declaration(name.as_any())?;
        Ok(self
            .inner
            .axiom_footprint(id)
            .into_iter()
            .map(|axiom| self.inner.display_name(axiom).to_string())
            .collect())
    }

    /// [`Self::axiom_footprint`] as handles rather than rendered names.
    ///
    /// # Errors
    ///
    /// Raises `KeyError` if nothing is declared under `name`.
    fn axiom_footprint_ids(&mut self, name: NameLike<'_>) -> PyResult<Vec<PyNameId>> {
        let id = self.require_declaration(name.as_any())?;
        Ok(self
            .inner
            .axiom_footprint(id)
            .into_iter()
            .map(|axiom| self.wrap_name(axiom))
            .collect())
    }

    /// Whether `name` rests on no trusted declaration at all.
    ///
    /// Defined **only** through [`Self::axiom_footprint`], never by a variant
    /// test: the trusted surface is `Axiom | Opaque | Quotient`, since `Opaque`
    /// has no proof body and the quotient package admits `Quot.sound`.
    ///
    /// # Errors
    ///
    /// Raises `KeyError` if nothing is declared under `name`.
    fn is_axiom_free(&mut self, name: NameLike<'_>) -> PyResult<bool> {
        Ok(self.axiom_footprint(name)?.is_empty())
    }

    /// Every declaration reachable from `name`, rendered and sorted.
    ///
    /// # Errors
    ///
    /// Raises `KeyError` if nothing is declared under `name`.
    fn declaration_dependency_closure(&mut self, name: NameLike<'_>) -> PyResult<Vec<String>> {
        let id = self.require_declaration(name.as_any())?;
        Ok(self
            .inner
            .declaration_dependency_closure(id)
            .into_iter()
            .map(|dep| self.inner.display_name(dep).to_string())
            .collect())
    }

    /// The declarations `name` refers to directly, including non-theorems.
    ///
    /// # Errors
    ///
    /// Raises `KeyError` if nothing is declared under `name`.
    fn declaration_dependencies(&mut self, name: NameLike<'_>) -> PyResult<Vec<String>> {
        let id = self.require_declaration(name.as_any())?;
        Ok(self
            .inner
            .declaration_dependencies(id)
            .into_iter()
            .map(|dep| self.inner.display_name(dep).to_string())
            .collect())
    }

    /// The declarations referenced directly by `name`'s type, never its value.
    ///
    /// # Errors
    ///
    /// Raises `KeyError` if nothing is declared under `name`.
    fn declaration_type_dependencies(&mut self, name: NameLike<'_>) -> PyResult<Vec<String>> {
        let id = self.require_declaration(name.as_any())?;
        Ok(self
            .inner
            .declaration_type_dependencies(id)
            .into_iter()
            .map(|dep| self.inner.display_name(dep).to_string())
            .collect())
    }

    /// The theorem declarations `name` refers to directly (self-reference dropped).
    ///
    /// # Errors
    ///
    /// Raises `KeyError` if nothing is declared under `name`.
    fn theorem_dependencies(&mut self, name: NameLike<'_>) -> PyResult<Vec<String>> {
        let id = self.require_declaration(name.as_any())?;
        Ok(self
            .inner
            .theorem_dependencies(id)
            .into_iter()
            .map(|dep| self.inner.display_name(dep).to_string())
            .collect())
    }

    /// Every declaration the given expressions mention.
    ///
    /// # Errors
    ///
    /// Raises `EpochError` if a handle came from another kernel.
    fn declarations_reached(&self, roots: Vec<PyExprId>) -> PyResult<Vec<String>> {
        let roots = roots
            .iter()
            .map(|root| self.expr_of(*root))
            .collect::<PyResult<Vec<_>>>()?;
        Ok(self
            .inner
            .declarations_reached(&roots)
            .into_iter()
            .map(|name| self.inner.display_name(name).to_string())
            .collect())
    }

    // -- rendering and export ---------------------------------------------

    /// The expression in Lean-ish source syntax.
    ///
    /// # Errors
    ///
    /// Raises `EpochError` if the handle came from another kernel.
    fn render_lean(&self, expr: PyExprId) -> PyResult<String> {
        let id = self.expr_of(expr)?;
        Ok(self.inner.render_lean(id))
    }

    /// The declaration as a Lean command.
    ///
    /// # Errors
    ///
    /// Raises `EpochError` if the declaration names another kernel's handles.
    fn render_lean_decl(&self, declaration: PyRef<'_, PyDeclaration>) -> PyResult<String> {
        epoch_guard(self.epoch, declaration.epoch, "Declaration")?;
        Ok(self.inner.render_lean_decl(&declaration.inner))
    }

    /// A self-contained Lean module proving `theorem_name : goal := proof`.
    ///
    /// # Errors
    ///
    /// Raises `EpochError` if a handle came from another kernel.
    fn render_lean_module(
        &self,
        theorem_name: &str,
        goal: PyExprId,
        proof: PyExprId,
    ) -> PyResult<String> {
        let goal = self.expr_of(goal)?;
        let proof = self.expr_of(proof)?;
        Ok(self.inner.render_lean_module(theorem_name, goal, proof))
    }

    /// [`Self::render_lean_module`] with shared closed sub-DAGs hoisted.
    ///
    /// Semantically equivalent and often far smaller for a hash-consed proof
    /// whose tree rendering re-expands shared subterms.
    ///
    /// # Errors
    ///
    /// Raises `EpochError` if a handle came from another kernel.
    fn render_lean_module_compact(
        &self,
        theorem_name: &str,
        goal: PyExprId,
        proof: PyExprId,
    ) -> PyResult<String> {
        let goal = self.expr_of(goal)?;
        let proof = self.expr_of(proof)?;
        Ok(self
            .inner
            .render_lean_module_compact(theorem_name, goal, proof))
    }

    /// The declaration closure of `roots` as official `lean4export` NDJSON
    /// (format 3.1.0).
    ///
    /// `lean_version` is the Lean release the stream targets. The producer
    /// label is fixed to `axeyum-lean-kernel` rather than a plausible-looking
    /// Lean commit hash, because nothing in this stream came from a Lean binary.
    ///
    /// # Errors
    ///
    /// Raises `EpochError` if a handle came from another kernel, and
    /// `AxeyumError` for an empty root set, a root absent from the environment,
    /// or a construct the format cannot carry.
    fn render_lean4export_ndjson_roots(
        &self,
        lean_version: &str,
        roots: Vec<PyNameId>,
    ) -> PyResult<String> {
        let roots = self.names_of(&roots)?;
        let metadata = Lean4ExportMetadata::axeyum(lean_version);
        self.inner
            .render_lean4export_ndjson_roots(&metadata, &roots)
            .map_err(|error| AxeyumError::new_err(format!("{error:?}")))
    }

    fn __repr__(&self) -> String {
        format!(
            "Kernel(epoch={}, declarations={})",
            self.epoch,
            self.inner.environment().len()
        )
    }
}

// ---------------------------------------------------------------------------
// Module-level functions
// ---------------------------------------------------------------------------

/// The process-wide prelude reuse counters (ADR-0464).
///
/// `hits` rising between two `Kernel()` builds of the same prelude is the only
/// evidence the cache actually ran; equal timings prove nothing.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyfunction(module = "axeyum._native.kernel")
)]
#[pyfunction]
fn prelude_cache_stats() -> PyPreludeCacheStats {
    let stats = prelude_cache::stats();
    PyPreludeCacheStats {
        hits: stats.hits,
        misses: stats.misses,
        templates_built: stats.templates_built,
    }
}

/// Whether process-wide prelude reuse is enabled (`AXEYUM_PRELUDE_CACHE=0`
/// disables it; read once per process).
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyfunction(module = "axeyum._native.kernel")
)]
#[pyfunction]
fn prelude_cache_enabled() -> bool {
    prelude_cache::enabled()
}

/// The canonical arena-independent SHA-256 identity of one declaration.
///
/// # Errors
///
/// Raises `EpochError` for a foreign handle, `KeyError` if the name is not
/// declared, and `AxeyumError` if the declaration cannot be hashed completely.
// PyO3 extracts OWNED values across the FFI edge: a `&[T]` or a `&PyRef<T>`
// cannot be built from a Python object, so every argument below is by value
// whether or not the body consumes it.
#[allow(clippy::needless_pass_by_value)]
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyfunction(module = "axeyum._native.kernel.identity")
)]
#[pyfunction]
fn canonical_declaration_sha256(
    mut kernel: PyRefMut<'_, PyKernel>,
    name: NameLike<'_>,
) -> PyResult<String> {
    let id = kernel.require_declaration(name.as_any())?;
    lean_import::canonical_declaration_sha256(&kernel.inner, id).map_err(AxeyumError::new_err)
}

/// The canonical arena-independent SHA-256 identity of one expression.
///
/// # Errors
///
/// Raises `EpochError` for a foreign handle and `AxeyumError` if the expression
/// DAG cannot be hashed completely.
// PyO3 extracts OWNED values across the FFI edge: a `&[T]` or a `&PyRef<T>`
// cannot be built from a Python object, so every argument below is by value
// whether or not the body consumes it.
#[allow(clippy::needless_pass_by_value)]
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyfunction(module = "axeyum._native.kernel.identity")
)]
#[pyfunction]
fn canonical_expression_sha256(
    kernel: PyRef<'_, PyKernel>,
    expression: PyExprId,
) -> PyResult<String> {
    let id = kernel.expr_of(expression)?;
    lean_import::canonical_expression_sha256(&kernel.inner, id).map_err(AxeyumError::new_err)
}

/// An expression identity that ignores cosmetic binder names, so expressions
/// from independently constructed kernels can be compared for alpha
/// equivalence.
///
/// # Errors
///
/// Raises `EpochError` for a foreign handle and `AxeyumError` if the expression
/// DAG cannot be hashed completely.
// PyO3 extracts OWNED values across the FFI edge: a `&[T]` or a `&PyRef<T>`
// cannot be built from a Python object, so every argument below is by value
// whether or not the body consumes it.
#[allow(clippy::needless_pass_by_value)]
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyfunction(module = "axeyum._native.kernel.identity")
)]
#[pyfunction]
fn canonical_alpha_expression_sha256(
    kernel: PyRef<'_, PyKernel>,
    expression: PyExprId,
) -> PyResult<String> {
    let id = kernel.expr_of(expression)?;
    lean_import::canonical_alpha_expression_sha256(&kernel.inner, id).map_err(AxeyumError::new_err)
}

/// A conservative cross-kernel *type shape* identity.
///
/// It ignores binder names, binder info and universe-parameter spelling, and it
/// does **not** unfold definitions. Equality is evidence of that narrow
/// structural compatibility only — never general definitional equality, and
/// never authority to reuse a declaration.
///
/// # Errors
///
/// Raises `EpochError` for a foreign handle and `AxeyumError` if the expression
/// DAG cannot be hashed completely.
// PyO3 extracts OWNED values across the FFI edge: a `&[T]` or a `&PyRef<T>`
// cannot be built from a Python object, so every argument below is by value
// whether or not the body consumes it.
#[allow(clippy::needless_pass_by_value)]
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyfunction(module = "axeyum._native.kernel.identity")
)]
#[pyfunction]
fn canonical_kernel_type_shape_sha256(
    kernel: PyRef<'_, PyKernel>,
    expression: PyExprId,
) -> PyResult<String> {
    let id = kernel.expr_of(expression)?;
    lean_import::canonical_kernel_type_shape_sha256(&kernel.inner, id).map_err(AxeyumError::new_err)
}

/// The canonical arena-independent SHA-256 identity of one universe level.
///
/// # Errors
///
/// Raises `EpochError` for a foreign handle.
// PyO3 extracts OWNED values across the FFI edge: a `&[T]` or a `&PyRef<T>`
// cannot be built from a Python object, so every argument below is by value
// whether or not the body consumes it.
#[allow(clippy::needless_pass_by_value)]
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyfunction(module = "axeyum._native.kernel.identity")
)]
#[pyfunction]
fn canonical_level_sha256(kernel: PyRef<'_, PyKernel>, level: PyLevelId) -> PyResult<String> {
    let id = kernel.level_of(level)?;
    Ok(lean_import::canonical_level_sha256(&kernel.inner, id))
}

/// Builds the `kernel.identity` submodule.
fn register_identity<'py>(parent: &Bound<'py, PyModule>) -> PyResult<Bound<'py, PyModule>> {
    let py = parent.py();
    let module = PyModule::new(py, "axeyum._native.kernel.identity")?;
    module.add_function(wrap_pyfunction!(canonical_declaration_sha256, &module)?)?;
    module.add_function(wrap_pyfunction!(canonical_expression_sha256, &module)?)?;
    module.add_function(wrap_pyfunction!(
        canonical_alpha_expression_sha256,
        &module
    )?)?;
    module.add_function(wrap_pyfunction!(
        canonical_kernel_type_shape_sha256,
        &module
    )?)?;
    module.add_function(wrap_pyfunction!(canonical_level_sha256, &module)?)?;
    parent.add("identity", &module)?;
    Ok(module)
}

/// Builds the `kernel` submodule.
///
/// # Errors
///
/// Propagates any Python error raised while creating or populating the module.
pub(crate) fn register<'py>(parent: &Bound<'py, PyModule>) -> PyResult<Bound<'py, PyModule>> {
    let py = parent.py();
    // The FULL dotted name, so `repr(axeyum.kernel)` and every traceback name
    // the module the way an import statement spells it.
    let module = PyModule::new(py, "axeyum._native.kernel")?;
    module.add_class::<PyKernel>()?;
    module.add_class::<PyDeclaration>()?;
    module.add_class::<PyPrelude>()?;
    module.add_class::<PyPreludeCacheStats>()?;
    module.add_class::<PyNameId>()?;
    module.add_class::<PyLevelId>()?;
    module.add_class::<PyExprId>()?;
    module.add_class::<PyExprNode>()?;
    module.add_class::<PyBinderInfo>()?;
    module.add_class::<PyLit>()?;
    module.add("EpochError", py.get_type::<EpochError>())?;
    module.add("KernelError", py.get_type::<KernelError>())?;
    module.add_function(wrap_pyfunction!(prelude_cache_stats, &module)?)?;
    module.add_function(wrap_pyfunction!(prelude_cache_enabled, &module)?)?;
    let identity_module = register_identity(&module)?;
    // `add_submodule` sets the attribute but not `sys.modules`, so without this
    // `import axeyum._native.kernel.identity` fails while the attribute works --
    // the same split `lib.rs` fixes for the top-level submodules.
    py.import("sys")?
        .getattr("modules")?
        .set_item("axeyum._native.kernel.identity", &identity_module)?;
    parent.add("kernel", &module)?;
    Ok(module)
}

// See `crate::error`: an exception is a `PyErr` type, not a `#[pyclass]`, so the
// stub record has to be submitted separately. The four members of `KernelError`
// are attached with `setattr` at the RAISE site, so they appear in no signature
// and no generator can discover them -- they are declared here or nowhere.
#[cfg(feature = "stub-gen")]
mod stub {
    use std::collections::HashMap;

    use super::{EpochError, KernelError};
    use crate::error::AxeyumError;
    use crate::stub_info::stub_exception;

    stub_exception!(
        "axeyum._native.kernel",
        EpochError,
        AxeyumError,
        "A handle was used with a kernel that did not intern it."
    );
    stub_exception!(
        "axeyum._native.kernel",
        KernelError,
        AxeyumError,
        "The kernel refused a declaration, an inference, or an inductive.",
        "variant": String = "The Rust `KernelError` variant name. Never match on the message text.",
        "fields": HashMap<String, String> = "The variant's payload, rendered field by field.",
        "names": HashMap<String, String> = "Payload names that resolve to a declaration in the environment.",
        "debug": String = "The full Rust `Debug` rendering of the refusal.",
    );
}

/// A declaration name: a `str` in Lean's dotted spelling, or an interned
/// [`PyNameId`] this kernel minted.
///
/// The accessors read it with `PyKernel::resolve`, which needs the untyped
/// handle, so the Rust parameter would otherwise be `&Bound<'_, PyAny>` and the
/// generated stub would say `typing.Any` -- hiding the one distinction that
/// actually matters here, which is that a `NameId` interned by ANOTHER kernel
/// is refused rather than silently denoting a different declaration.
pub(crate) struct NameLike<'py>(Bound<'py, PyAny>);

impl<'py> NameLike<'py> {
    /// The wrapped object, to resolve against a kernel.
    pub(crate) fn as_any(&self) -> &Bound<'py, PyAny> {
        &self.0
    }
}

impl<'py> FromPyObject<'_, 'py> for NameLike<'py> {
    type Error = PyErr;

    fn extract(object: pyo3::Borrowed<'_, 'py, PyAny>) -> Result<Self, Self::Error> {
        Ok(Self(object.to_owned()))
    }
}

#[cfg(feature = "stub-gen")]
impl pyo3_stub_gen::PyStubType for NameLike<'_> {
    fn type_input() -> pyo3_stub_gen::TypeInfo {
        use pyo3_stub_gen::PyStubType;
        <String as PyStubType>::type_input() | <PyNameId as PyStubType>::type_output()
    }

    fn type_output() -> pyo3_stub_gen::TypeInfo {
        Self::type_input()
    }
}
