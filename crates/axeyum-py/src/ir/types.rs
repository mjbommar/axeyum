//! Handles, sorts, term nodes and the two IR exceptions.
//!
//! # The epoch invariant
//!
//! `axeyum_ir::TermId` and its siblings are bare `u32` indices with **no arena
//! identity in the type**. Passing a `TermId` minted by arena A to arena B is a
//! Rust-side panic (an out-of-range index), not an error — and that path is
//! reachable from Python. Every handle here therefore carries the epoch of the
//! [`Arena`](crate::ir::arena::Arena) that minted it, and every consuming call
//! checks it. This is the binding's one non-negotiable invariant.

#![allow(
    // PyO3's calling convention hands `PyRef`/`PyRefMut` guards and owned
    // `Vec<Term>` arguments in by value; there is no by-reference form.
    clippy::needless_pass_by_value,
    clippy::trivially_copy_pass_by_ref
)]

use axeyum_ir::{
    ArraySortKey, ConstructorId, DatatypeId, FuncId, IrError, Op, Sort, SortId, SymbolId, TermId,
    TermNode, TermStats,
};
use pyo3::create_exception;
use pyo3::prelude::*;
use pyo3::types::{PyDict, PyString, PyTuple};

use crate::error::AxeyumError;

create_exception!(
    axeyum,
    EpochError,
    AxeyumError,
    "A handle was used against an arena other than the one that minted it.\n\nThe Rust IR has no arena identity in `TermId`/`SymbolId`/..., so this would be\nan out-of-range index (a panic) without the binding's epoch check."
);
create_exception!(
    axeyum,
    SortError,
    AxeyumError,
    "A term constructor rejected its operands (`axeyum_ir::IrError`).\n\nSort mismatches, widths outside `1..=65536`, out-of-range `extract` bounds and\nconstants that do not fit their declared width all arrive here."
);

/// Raises [`EpochError`] when `found` is not the arena epoch `expected`.
pub(crate) fn check_epoch(expected: u64, found: u64, what: &str) -> PyResult<()> {
    if expected == found {
        return Ok(());
    }
    Err(EpochError::new_err(format!(
        "{what} was minted by arena epoch {found}; this call is against arena epoch {expected}"
    )))
}

/// Maps an IR construction/evaluation error onto [`SortError`].
pub(crate) fn map_ir_error(error: &IrError) -> PyErr {
    SortError::new_err(error.to_string())
}

macro_rules! handle {
    ($py_name:literal, $rust:ident, $inner:ty, $doc:literal) => {
        #[doc = $doc]
        #[cfg_attr(
            feature = "stub-gen",
            pyo3_stub_gen::derive::gen_stub_pyclass(module = "axeyum._native.ir")
        )]
        #[pyclass(frozen, from_py_object, module = "axeyum", name = $py_name)]
        #[derive(Debug, Clone, Copy, PartialEq, Eq)]
        pub struct $rust {
            pub(crate) epoch: u64,
            pub(crate) id: $inner,
        }

        impl $rust {
            pub(crate) fn new(epoch: u64, id: $inner) -> Self {
                Self { epoch, id }
            }

            /// The wrapped handle, after confirming it belongs to `epoch`.
            pub(crate) fn resolve(&self, epoch: u64) -> PyResult<$inner> {
                check_epoch(epoch, self.epoch, $py_name)?;
                Ok(self.id)
            }
        }

        #[cfg_attr(feature = "stub-gen", pyo3_stub_gen::derive::gen_stub_pymethods)]
        #[pymethods]
        impl $rust {
            /// The epoch of the arena that minted this handle.
            #[getter]
            fn epoch(&self) -> u64 {
                self.epoch
            }

            /// The dense index inside the owning arena.
            ///
            /// Informational only: the Rust handle's field is private, so a raw
            /// index cannot be turned back into a handle. That is deliberate —
            /// it forces every handle through the arena that owns it.
            #[getter]
            fn raw(&self) -> u32 {
                u32::try_from(self.id.index()).unwrap_or(u32::MAX)
            }

            fn __repr__(&self) -> String {
                format!(
                    "{}(epoch={}, raw={})",
                    $py_name,
                    self.epoch,
                    self.id.index()
                )
            }

            fn __eq__(&self, other: &Bound<'_, PyAny>) -> bool {
                other
                    .cast::<Self>()
                    .is_ok_and(|other| *self == *other.get())
            }

            fn __hash__(&self) -> u64 {
                (self.epoch << 32) ^ (self.id.index() as u64)
            }
        }
    };
}

handle!(
    "Term",
    Term,
    TermId,
    "A term in one [`Arena`](axeyum.ir.Arena). Frozen, hashable, and valid only against the arena whose `epoch` it carries."
);
handle!(
    "Symbol",
    Symbol,
    SymbolId,
    "A declared 0-ary constant (an SMT-LIB `declare-fun` with no arguments)."
);
handle!(
    "Func",
    Func,
    FuncId,
    "A declared uninterpreted function symbol."
);
handle!(
    "SortRef",
    SortRef,
    SortId,
    "A declared uninterpreted carrier sort.\n\nNamed `SortRef`, not `SortId`, so it cannot be confused with the structural [`Sort`](axeyum.ir.Sort) value."
);
handle!("Datatype", Datatype, DatatypeId, "A declared datatype.");
handle!(
    "Constructor",
    Constructor,
    ConstructorId,
    "One constructor of a declared datatype."
);

/// A sort (type) of a term.
///
/// Construct with the class methods (`Sort.bool()`, `Sort.bv(8)`,
/// `Sort.array(index, element)`, …). `Sort.datatype(...)` and
/// `Sort.uninterpreted(...)` are arena-relative and carry that arena's epoch;
/// every other sort is arena-independent (`epoch == 0`).
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyclass(module = "axeyum._native.ir")
)]
#[pyclass(frozen, from_py_object, module = "axeyum", name = "Sort")]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct PySort {
    pub(crate) epoch: u64,
    pub(crate) sort: Sort,
}

impl PySort {
    pub(crate) fn universal(sort: Sort) -> Self {
        Self { epoch: 0, sort }
    }

    /// Builds a Python sort, inheriting `epoch` for the two arena-relative
    /// variants and staying arena-independent otherwise.
    pub(crate) fn bound(epoch: u64, sort: Sort) -> Self {
        Self { epoch, sort }
    }

    /// The wrapped sort, after confirming any arena-relative component belongs
    /// to `epoch`.
    pub(crate) fn resolve(&self, epoch: u64) -> PyResult<Sort> {
        if self.epoch != 0 {
            check_epoch(epoch, self.epoch, "Sort")?;
        }
        Ok(self.sort)
    }
}

#[cfg_attr(feature = "stub-gen", pyo3_stub_gen::derive::gen_stub_pymethods)]
#[pymethods]
impl PySort {
    /// The Boolean sort.
    #[staticmethod]
    fn bool() -> Self {
        Self::universal(Sort::Bool)
    }

    /// A fixed-width bit-vector sort; `width` must be in `1..=65536`.
    #[staticmethod]
    fn bv(width: u32) -> PyResult<Self> {
        if width == 0 || width > axeyum_ir::MAX_BV_WIDTH {
            return Err(map_ir_error(&IrError::InvalidWidth(width)));
        }
        Ok(Self::universal(Sort::BitVec(width)))
    }

    /// The mathematical integer sort.
    #[staticmethod]
    fn int() -> Self {
        Self::universal(Sort::Int)
    }

    /// The mathematical real sort.
    #[staticmethod]
    fn real() -> Self {
        Self::universal(Sort::Real)
    }

    /// The five-element SMT-LIB rounding-mode sort.
    #[staticmethod]
    fn rounding_mode() -> Self {
        Self::universal(Sort::RoundingMode)
    }

    /// An IEEE 754 floating-point sort of format `(exp, sig)` bits.
    #[staticmethod]
    fn float(exp: u32, sig: u32) -> Self {
        Self::universal(Sort::Float { exp, sig })
    }

    /// The SMT-LIB `String` sort — `Seq(BitVec(18))` (ADR-0051).
    #[staticmethod]
    fn string() -> Self {
        Self::universal(Sort::string())
    }

    /// A total map from `index` to `element`.
    ///
    /// Nested arrays are not representable: both components must be scalar.
    #[staticmethod]
    fn array(index: &PySort, element: &PySort) -> PyResult<Self> {
        let epoch = merged_epoch(index, element)?;
        let index_key = array_key(index.sort)?;
        let element_key = array_key(element.sort)?;
        Ok(Self {
            epoch,
            sort: Sort::Array {
                index: index_key,
                element: element_key,
            },
        })
    }

    /// A homogeneous sequence over a scalar `element` sort.
    #[staticmethod]
    fn seq(element: &PySort) -> PyResult<Self> {
        Ok(Self {
            epoch: element.epoch,
            sort: Sort::Seq(array_key(element.sort)?),
        })
    }

    /// The sort of a declared datatype.
    #[staticmethod]
    fn datatype(datatype: Datatype) -> Self {
        Self {
            epoch: datatype.epoch,
            sort: Sort::Datatype(datatype.id),
        }
    }

    /// The sort of a declared uninterpreted carrier.
    #[staticmethod]
    fn uninterpreted(sort: SortRef) -> Self {
        Self {
            epoch: sort.epoch,
            sort: Sort::Uninterpreted(sort.id),
        }
    }

    /// A stable short tag: `"Bool"`, `"BitVec"`, `"Array"`, `"Int"`, `"Real"`,
    /// `"RoundingMode"`, `"Datatype"`, `"Uninterpreted"`, `"Float"`, `"Seq"`.
    #[getter]
    fn kind(&self) -> &'static str {
        match self.sort {
            Sort::Bool => "Bool",
            Sort::BitVec(_) => "BitVec",
            Sort::Array { .. } => "Array",
            Sort::Int => "Int",
            Sort::Real => "Real",
            Sort::RoundingMode => "RoundingMode",
            Sort::Datatype(_) => "Datatype",
            Sort::Uninterpreted(_) => "Uninterpreted",
            Sort::Float { .. } => "Float",
            Sort::Seq(_) => "Seq",
        }
    }

    /// The epoch of the arena this sort is relative to; `0` when it is not.
    #[getter]
    fn epoch(&self) -> u64 {
        self.epoch
    }

    /// The bit-vector width, or `None`. A float is NOT a bit-vector here.
    fn bv_width(&self) -> Option<u32> {
        self.sort.bv_width()
    }

    /// The width this sort bit-blasts to (`exp + sig` for a float), or `None`.
    fn lowered_width(&self) -> Option<u32> {
        self.sort.lowered_width()
    }

    /// Whether this is the Boolean sort.
    fn is_bool(&self) -> bool {
        self.sort.is_bool()
    }

    /// The `(exp, sig)` format of a floating-point sort, else `None`.
    fn float_format(&self) -> Option<(u32, u32)> {
        self.sort.float_format()
    }

    /// The `(index, element)` component sorts of an array sort, else `None`.
    fn array_sorts(&self) -> Option<(PySort, PySort)> {
        self.sort.array_sorts().map(|(index, element)| {
            (
                Self {
                    epoch: self.epoch,
                    sort: index,
                },
                Self {
                    epoch: self.epoch,
                    sort: element,
                },
            )
        })
    }

    /// The element sort of a sequence sort, else `None`.
    fn seq_element(&self) -> Option<Self> {
        match self.sort {
            Sort::Seq(element) => Some(Self {
                epoch: self.epoch,
                sort: element.to_sort(),
            }),
            _ => None,
        }
    }

    fn __str__(&self) -> String {
        self.sort.to_string()
    }

    fn __repr__(&self) -> String {
        format!("Sort({})", self.sort)
    }

    fn __eq__(&self, other: &Bound<'_, PyAny>) -> bool {
        other
            .cast::<Self>()
            .is_ok_and(|other| self.sort == other.get().sort && self.epoch == other.get().epoch)
    }

    fn __hash__(&self) -> u64 {
        let mut hash = self.epoch.wrapping_mul(0x9E37_79B9_7F4A_7C15);
        hash ^= self
            .sort
            .to_string()
            .bytes()
            .fold(1_469_598_103_934_665_603_u64, |acc, byte| {
                (acc ^ u64::from(byte)).wrapping_mul(1_099_511_628_211)
            });
        hash
    }
}

/// The common epoch of two sorts, or an error when they belong to two arenas.
fn merged_epoch(left: &PySort, right: &PySort) -> PyResult<u64> {
    match (left.epoch, right.epoch) {
        (0, other) | (other, 0) => Ok(other),
        (a, b) if a == b => Ok(a),
        (a, b) => Err(EpochError::new_err(format!(
            "sorts belong to different arenas (epochs {a} and {b})"
        ))),
    }
}

/// The array/sequence component key of a scalar sort.
fn array_key(sort: Sort) -> PyResult<ArraySortKey> {
    ArraySortKey::from_sort(sort).ok_or_else(|| {
        SortError::new_err(format!(
            "{sort} cannot be an array index/element or a sequence element (nested arrays and \
             nested sequences are deferred in the IR)"
        ))
    })
}

/// The stable SMT-LIB-flavoured name of an operator.
///
/// One name per `axeyum_ir::Op` variant; parameterized operators (`extract`,
/// the extensions, the rotates, `int2bv`, the datatype trio) carry their
/// parameters in [`PyTermNode::op_params`] rather than in the name.
pub(crate) fn op_name(op: Op) -> &'static str {
    match op {
        Op::BoolNot => "not",
        Op::BoolAnd => "and",
        Op::BoolOr => "or",
        Op::BoolXor => "xor",
        Op::BoolImplies => "=>",
        Op::BvNot => "bvnot",
        Op::BvAnd => "bvand",
        Op::BvOr => "bvor",
        Op::BvXor => "bvxor",
        Op::BvNand => "bvnand",
        Op::BvNor => "bvnor",
        Op::BvXnor => "bvxnor",
        Op::BvNeg => "bvneg",
        Op::BvAdd => "bvadd",
        Op::BvSub => "bvsub",
        Op::BvMul => "bvmul",
        Op::BvUdiv => "bvudiv",
        Op::BvUrem => "bvurem",
        Op::BvSdiv => "bvsdiv",
        Op::BvSrem => "bvsrem",
        Op::BvSmod => "bvsmod",
        Op::BvShl => "bvshl",
        Op::BvLshr => "bvlshr",
        Op::BvAshr => "bvashr",
        Op::BvUlt => "bvult",
        Op::BvUle => "bvule",
        Op::BvUgt => "bvugt",
        Op::BvUge => "bvuge",
        Op::BvSlt => "bvslt",
        Op::BvSle => "bvsle",
        Op::BvSgt => "bvsgt",
        Op::BvSge => "bvsge",
        Op::Eq => "=",
        Op::Ite => "ite",
        Op::BvComp => "bvcomp",
        Op::Extract { .. } => "extract",
        Op::Concat => "concat",
        Op::ZeroExt { .. } => "zero_extend",
        Op::SignExt { .. } => "sign_extend",
        Op::RotateLeft { .. } => "rotate_left",
        Op::RotateRight { .. } => "rotate_right",
        Op::Select => "select",
        Op::Store => "store",
        Op::ConstArray { .. } => "const_array",
        Op::IntToReal => "to_real",
        Op::RealToInt => "to_int",
        Op::RealIsInt => "is_int",
        Op::Bv2Nat => "bv2nat",
        Op::Int2Bv { .. } => "int2bv",
        Op::Apply(_) => "apply",
        Op::IntNeg => "int_neg",
        Op::IntAdd => "int_add",
        Op::IntSub => "int_sub",
        Op::IntMul => "int_mul",
        Op::IntDiv => "int_div",
        Op::IntMod => "int_mod",
        Op::IntAbs => "int_abs",
        Op::IntPow2 => "int_pow2",
        Op::IntLt => "int_lt",
        Op::IntLe => "int_le",
        Op::IntGt => "int_gt",
        Op::IntGe => "int_ge",
        Op::RealNeg => "real_neg",
        Op::RealAdd => "real_add",
        Op::RealSub => "real_sub",
        Op::RealMul => "real_mul",
        Op::RealDiv => "real_div",
        Op::RealLt => "real_lt",
        Op::RealLe => "real_le",
        Op::RealGt => "real_gt",
        Op::RealGe => "real_ge",
        Op::Forall(_) => "forall",
        Op::Exists(_) => "exists",
        Op::DtConstruct { .. } => "dt_construct",
        Op::DtSelect { .. } => "dt_select",
        Op::DtTest(_) => "dt_test",
        Op::FpFromBits { .. } => "fp_from_bits",
        Op::RoundingModeFromBits => "rounding_mode_from_bits",
        Op::SeqLen => "seq_len",
        Op::SeqEmpty(_) => "seq_empty",
        Op::SeqUnit => "seq_unit",
        Op::SeqConcat => "seq_concat",
    }
}

/// The parameters an operator carries in itself rather than in its arguments.
fn op_params(py: Python<'_>, epoch: u64, op: Op) -> PyResult<Bound<'_, PyDict>> {
    let params = PyDict::new(py);
    match op {
        Op::Extract { hi, lo } => {
            params.set_item("hi", hi)?;
            params.set_item("lo", lo)?;
        }
        Op::ZeroExt { by }
        | Op::SignExt { by }
        | Op::RotateLeft { by }
        | Op::RotateRight { by } => params.set_item("by", by)?,
        Op::ConstArray { index } => {
            params.set_item("index", PySort::bound(epoch, index.to_sort()))?;
        }
        Op::Int2Bv { width } => params.set_item("width", width)?,
        Op::Apply(func) => params.set_item("func", Func::new(epoch, func))?,
        Op::Forall(symbol) | Op::Exists(symbol) => {
            params.set_item("var", Symbol::new(epoch, symbol))?;
        }
        Op::DtConstruct {
            constructor,
            datatype,
        } => {
            params.set_item("constructor", Constructor::new(epoch, constructor))?;
            params.set_item("datatype", Datatype::new(epoch, datatype))?;
        }
        Op::DtSelect { constructor, index } => {
            params.set_item("constructor", Constructor::new(epoch, constructor))?;
            params.set_item("index", index)?;
        }
        Op::DtTest(constructor) => {
            params.set_item("constructor", Constructor::new(epoch, constructor))?;
        }
        Op::FpFromBits { exp, sig } => {
            params.set_item("exp", exp)?;
            params.set_item("sig", sig)?;
        }
        Op::SeqEmpty(element) => {
            params.set_item("element", PySort::bound(epoch, element.to_sort()))?;
        }
        _ => {}
    }
    Ok(params)
}

/// One structural node of a term, copied out of the arena.
///
/// Owned, so a Python walker can hold it while the arena keeps being built.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyclass(module = "axeyum._native.ir")
)]
#[pyclass(frozen, module = "axeyum", name = "TermNode")]
pub struct PyTermNode {
    kind: &'static str,
    op: Option<&'static str>,
    op_params: Py<PyDict>,
    args: Py<PyTuple>,
    symbol: Option<Symbol>,
    value: Option<Py<PyAny>>,
}

impl PyTermNode {
    /// Copies `node` out of the arena at `epoch`.
    pub(crate) fn build(py: Python<'_>, epoch: u64, node: &TermNode) -> PyResult<Self> {
        let empty_params = PyDict::new(py).unbind();
        let empty_args = PyTuple::empty(py).unbind();
        Ok(match node {
            TermNode::BoolConst(value) => Self {
                kind: "bool_const",
                op: None,
                op_params: empty_params,
                args: empty_args,
                symbol: None,
                value: Some(
                    crate::convert::value_to_py(py, &axeyum_ir::Value::Bool(*value))?.unbind(),
                ),
            },
            TermNode::BvConst { width, value } => Self {
                kind: "bv_const",
                op: None,
                op_params: empty_params,
                args: empty_args,
                symbol: None,
                value: Some(
                    crate::convert::value_to_py(
                        py,
                        &axeyum_ir::Value::Bv {
                            width: *width,
                            value: *value,
                        },
                    )?
                    .unbind(),
                ),
            },
            TermNode::WideBvConst(wide) => Self {
                kind: "bv_const",
                op: None,
                op_params: empty_params,
                args: empty_args,
                symbol: None,
                value: Some(
                    crate::convert::value_to_py(py, &axeyum_ir::Value::WideBv(wide.clone()))?
                        .unbind(),
                ),
            },
            TermNode::IntConst(value) => Self {
                kind: "int_const",
                op: None,
                op_params: empty_params,
                args: empty_args,
                symbol: None,
                value: Some(
                    crate::convert::value_to_py(py, &axeyum_ir::Value::Int(*value))?.unbind(),
                ),
            },
            TermNode::RealConst(value) => Self {
                kind: "real_const",
                op: None,
                op_params: empty_params,
                args: empty_args,
                symbol: None,
                value: Some(
                    crate::convert::value_to_py(py, &axeyum_ir::Value::Real(*value))?.unbind(),
                ),
            },
            TermNode::Symbol(symbol) => Self {
                kind: "symbol",
                op: None,
                op_params: empty_params,
                args: empty_args,
                symbol: Some(Symbol::new(epoch, *symbol)),
                value: None,
            },
            TermNode::App { op, args } => {
                let terms: Vec<Term> = args.iter().map(|&a| Term::new(epoch, a)).collect();
                Self {
                    kind: "app",
                    op: Some(op_name(*op)),
                    op_params: op_params(py, epoch, *op)?.unbind(),
                    args: PyTuple::new(py, terms)?.unbind(),
                    symbol: None,
                    value: None,
                }
            }
        })
    }
}

#[cfg_attr(feature = "stub-gen", pyo3_stub_gen::derive::gen_stub_pymethods)]
#[pymethods]
impl PyTermNode {
    /// `"bool_const"`, `"bv_const"`, `"int_const"`, `"real_const"`, `"symbol"`
    /// or `"app"`.
    #[getter]
    fn kind(&self) -> &'static str {
        self.kind
    }

    /// The operator name for an `"app"` node, else `None`.
    #[getter]
    fn op(&self) -> Option<&'static str> {
        self.op
    }

    /// Parameters the operator carries itself (`extract`'s `hi`/`lo`, a
    /// quantifier's bound `var`, …). Empty for un-parameterized operators.
    #[getter]
    fn op_params<'py>(&self, py: Python<'py>) -> PyResult<Bound<'py, PyDict>> {
        self.op_params.bind(py).copy()
    }

    /// The argument terms of an `"app"` node, in order.
    #[getter]
    fn args<'py>(&self, py: Python<'py>) -> Bound<'py, PyTuple> {
        self.args.bind(py).clone()
    }

    /// The declared symbol of a `"symbol"` node, else `None`.
    #[getter]
    fn symbol(&self) -> Option<Symbol> {
        self.symbol
    }

    /// The constant a `"*_const"` node carries, else `None`.
    #[getter]
    fn value<'py>(&self, py: Python<'py>) -> Option<Bound<'py, PyAny>> {
        self.value.as_ref().map(|value| value.bind(py).clone())
    }

    fn __repr__(&self, py: Python<'_>) -> String {
        match self.op {
            Some(op) => format!(
                "TermNode(kind='app', op={op:?}, args={})",
                self.args.bind(py).len()
            ),
            None => format!("TermNode(kind={:?})", self.kind),
        }
    }
}

/// Structural statistics over a set of root terms.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyclass(module = "axeyum._native.ir")
)]
#[pyclass(frozen, module = "axeyum", name = "TermStats")]
pub struct PyTermStats {
    stats: TermStats,
}

impl PyTermStats {
    pub(crate) fn new(stats: TermStats) -> Self {
        Self { stats }
    }
}

#[cfg_attr(feature = "stub-gen", pyo3_stub_gen::derive::gen_stub_pymethods)]
#[pymethods]
impl PyTermStats {
    /// Distinct nodes reachable from the roots (the shared DAG size).
    #[getter]
    fn dag_nodes(&self) -> u64 {
        self.stats.dag_nodes
    }

    /// Nodes the same formula would have with no sharing.
    #[getter]
    fn tree_nodes(&self) -> u64 {
        self.stats.tree_nodes
    }

    /// Longest root-to-leaf path.
    #[getter]
    fn max_depth(&self) -> u64 {
        self.stats.max_depth
    }

    /// Distinct declared symbols reachable from the roots.
    #[getter]
    fn distinct_symbols(&self) -> u64 {
        self.stats.distinct_symbols
    }

    /// `ite` nodes reachable from the roots.
    #[getter]
    fn ite_count(&self) -> u64 {
        self.stats.ite_count
    }

    /// Multiplication/division nodes reachable from the roots.
    #[getter]
    fn mul_div_count(&self) -> u64 {
        self.stats.mul_div_count
    }

    /// `tree_nodes / dag_nodes` — how much the DAG representation buys.
    fn sharing_ratio(&self) -> f64 {
        self.stats.sharing_ratio()
    }

    fn __repr__(&self) -> String {
        format!(
            "TermStats(dag_nodes={}, tree_nodes={}, max_depth={}, distinct_symbols={})",
            self.stats.dag_nodes,
            self.stats.tree_nodes,
            self.stats.max_depth,
            self.stats.distinct_symbols
        )
    }
}

/// The stable list of operator names [`PyTermNode::op`] can return.
pub(crate) fn all_op_names(py: Python<'_>) -> PyResult<Bound<'_, PyAny>> {
    const NAMES: &[&str] = &[
        "not",
        "and",
        "or",
        "xor",
        "=>",
        "bvnot",
        "bvand",
        "bvor",
        "bvxor",
        "bvnand",
        "bvnor",
        "bvxnor",
        "bvneg",
        "bvadd",
        "bvsub",
        "bvmul",
        "bvudiv",
        "bvurem",
        "bvsdiv",
        "bvsrem",
        "bvsmod",
        "bvshl",
        "bvlshr",
        "bvashr",
        "bvult",
        "bvule",
        "bvugt",
        "bvuge",
        "bvslt",
        "bvsle",
        "bvsgt",
        "bvsge",
        "=",
        "ite",
        "bvcomp",
        "extract",
        "concat",
        "zero_extend",
        "sign_extend",
        "rotate_left",
        "rotate_right",
        "select",
        "store",
        "const_array",
        "to_real",
        "to_int",
        "is_int",
        "bv2nat",
        "int2bv",
        "apply",
        "int_neg",
        "int_add",
        "int_sub",
        "int_mul",
        "int_div",
        "int_mod",
        "int_abs",
        "int_pow2",
        "int_lt",
        "int_le",
        "int_gt",
        "int_ge",
        "real_neg",
        "real_add",
        "real_sub",
        "real_mul",
        "real_div",
        "real_lt",
        "real_le",
        "real_gt",
        "real_ge",
        "forall",
        "exists",
        "dt_construct",
        "dt_select",
        "dt_test",
        "fp_from_bits",
        "rounding_mode_from_bits",
        "seq_len",
        "seq_empty",
        "seq_unit",
        "seq_concat",
    ];
    let items: Vec<Bound<'_, PyString>> =
        NAMES.iter().map(|name| PyString::new(py, name)).collect();
    py.get_type::<pyo3::types::PyFrozenSet>()
        .call1((PyTuple::new(py, items)?,))
}

// See `crate::error`: an exception is a `PyErr` type, not a `#[pyclass]`, so the
// stub record has to be submitted separately.
#[cfg(feature = "stub-gen")]
mod stub {
    use super::{EpochError, SortError};
    use crate::error::AxeyumError;
    use crate::stub_info::stub_exception;

    stub_exception!(
        "axeyum._native.ir",
        EpochError,
        AxeyumError,
        "A handle was used with an arena that did not mint it."
    );
    stub_exception!(
        "axeyum._native.ir",
        SortError,
        AxeyumError,
        "A term, value or sort was rejected by the IR."
    );
}
