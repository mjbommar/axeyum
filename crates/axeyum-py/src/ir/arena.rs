//! The Python-owned term arena and the full constructor set.
//!
//! # Naming
//!
//! A builder takes its SMT-LIB name whenever that name is a valid Python
//! identifier (`bvadd`, `bvudiv`, `concat`, `select`, `forall`); the Rust
//! builder name is used otherwise, because SMT-LIB spells integer and real
//! arithmetic with `+`, `-`, `div`, `<` (`int_add`, `int_div`, `int_lt`). The
//! Boolean connectives collide with Python keywords and take a trailing
//! underscore (`not_`, `and_`, `or_`, `xor_`).
//!
//! # Totality (SMT-LIB, verbatim)
//!
//! Every operator here is **total**. There is no `ZeroDivisionError` anywhere
//! in this module, and a caller who expects one will misread a correct answer:
//!
//! * `bvudiv(x, 0)` is all-ones; `bvurem(x, 0)` is `x`.
//! * `bvsdiv(x, 0)` is `-1` when `x >= 0` and `1` otherwise; `bvsrem(x, 0)` and
//!   `bvsmod(x, 0)` are both `x`.
//! * `int_div(a, 0)` is `0` and `int_mod(a, 0)` is `a` (the in-tree convention).
//! * `real_div(x, 0)` is `0` in the ground evaluator.
//! * Shifts by `>= width` saturate (to zero, or to the sign bits for `bvashr`);
//!   rotates normalize modulo the width at build time.

#![allow(
    // PyO3's calling convention hands `PyRef`/`PyRefMut` guards and owned
    // `Vec<Term>` arguments in by value; there is no by-reference form.
    clippy::needless_pass_by_value,
    clippy::trivially_copy_pass_by_ref
)]

use std::sync::atomic::{AtomicU64, Ordering};

use axeyum_ir::{IrError, Rational, Sort, TermArena, TermId};
use pyo3::prelude::*;
use pyo3::types::PyInt;

use crate::error::AxeyumError;
use crate::ir::types::{
    Constructor, Datatype, Func, PySort, PyTermNode, PyTermStats, SortRef, Symbol, Term,
    map_ir_error,
};

/// Hands out one epoch per [`Arena`], for the lifetime of the process.
static NEXT_EPOCH: AtomicU64 = AtomicU64::new(1);

/// A Python-owned term arena.
///
/// Terms are hash-consed inside it, and every handle it mints
/// ([`Term`](axeyum.ir.Term), [`Symbol`](axeyum.ir.Symbol), …) carries this
/// arena's `epoch`. Passing a handle from one arena to another raises
/// `EpochError` instead of panicking inside Rust.
#[pyclass(module = "axeyum", name = "Arena")]
pub struct Arena {
    pub(crate) arena: TermArena,
    pub(crate) epoch: u64,
}

impl Arena {
    /// Resolves a list of Python terms against this arena.
    pub(crate) fn resolve_terms(&self, terms: &[Term]) -> PyResult<Vec<TermId>> {
        terms.iter().map(|term| term.resolve(self.epoch)).collect()
    }

    /// Wraps a freshly built term.
    fn wrap(&self, id: TermId) -> Term {
        Term::new(self.epoch, id)
    }

    /// `{declared name: value}` for every symbol this arena knows a value for.
    pub(crate) fn named_values(
        &self,
        lookup: impl Fn(axeyum_ir::SymbolId) -> Option<axeyum_ir::Value>,
    ) -> Vec<(String, axeyum_ir::Value)> {
        let mut named: Vec<(String, axeyum_ir::Value)> = Vec::new();
        for (symbol, name, _sort) in self.arena.symbols() {
            if let Some(value) = lookup(symbol) {
                named.push((name.to_owned(), value));
            }
        }
        named
    }
}

#[pymethods]
impl Arena {
    /// Creates an empty arena with a fresh process-wide epoch.
    #[new]
    fn new() -> Self {
        Self {
            arena: TermArena::new(),
            epoch: NEXT_EPOCH.fetch_add(1, Ordering::Relaxed),
        }
    }

    /// This arena's identity. Every handle it mints carries the same number.
    #[getter]
    fn epoch_id(&self) -> u64 {
        self.epoch
    }

    /// Number of distinct interned terms.
    fn __len__(&self) -> usize {
        self.arena.len()
    }

    fn __repr__(&self) -> String {
        format!("Arena(epoch={}, terms={})", self.epoch, self.arena.len())
    }

    // ---------------------------------------------------------------- symbols

    /// Declares a 0-ary constant, or returns the existing one.
    ///
    /// Raises `SortError` when the name already exists with a different sort.
    fn declare(&mut self, name: &str, sort: &PySort) -> PyResult<Symbol> {
        let sort = sort.resolve(self.epoch)?;
        let symbol = self
            .arena
            .declare(name, sort)
            .map_err(|e| map_ir_error(&e))?;
        Ok(Symbol::new(self.epoch, symbol))
    }

    /// The declared symbol of that name, or `None`.
    fn find_symbol(&self, name: &str) -> Option<Symbol> {
        self.arena
            .find_symbol(name)
            .map(|symbol| Symbol::new(self.epoch, symbol))
    }

    /// The `(name, sort)` of a declared symbol.
    fn symbol(&self, symbol: Symbol) -> PyResult<(String, PySort)> {
        let symbol = symbol.resolve(self.epoch)?;
        let (name, sort) = self.arena.symbol(symbol);
        Ok((name.to_owned(), PySort::bound(self.epoch, sort)))
    }

    /// Every declared symbol as `(handle, name, sort)`, in declaration order.
    fn symbols(&self) -> Vec<(Symbol, String, PySort)> {
        self.arena
            .symbols()
            .map(|(symbol, name, sort)| {
                (
                    Symbol::new(self.epoch, symbol),
                    name.to_owned(),
                    PySort::bound(self.epoch, sort),
                )
            })
            .collect()
    }

    /// The term that reads a declared symbol.
    fn var(&mut self, symbol: Symbol) -> PyResult<Term> {
        let symbol = symbol.resolve(self.epoch)?;
        let id = self.arena.var(symbol);
        Ok(self.wrap(id))
    }

    // ------------------------------------------------ uninterpreted functions

    /// Declares an uninterpreted function.
    fn declare_fun(&mut self, name: &str, params: Vec<PySort>, result: &PySort) -> PyResult<Func> {
        let params: Vec<Sort> = params
            .iter()
            .map(|sort| sort.resolve(self.epoch))
            .collect::<PyResult<_>>()?;
        let result = result.resolve(self.epoch)?;
        let func = self
            .arena
            .declare_fun(name, &params, result)
            .map_err(|e| map_ir_error(&e))?;
        Ok(Func::new(self.epoch, func))
    }

    /// The declared function of that name, or `None`.
    fn find_function(&self, name: &str) -> Option<Func> {
        self.arena
            .find_function(name)
            .map(|func| Func::new(self.epoch, func))
    }

    /// The `(name, params, result)` of a declared function.
    fn function(&self, func: Func) -> PyResult<(String, Vec<PySort>, PySort)> {
        let func = func.resolve(self.epoch)?;
        let (name, params, result) = self.arena.function(func);
        Ok((
            name.to_owned(),
            params
                .iter()
                .map(|&sort| PySort::bound(self.epoch, sort))
                .collect(),
            PySort::bound(self.epoch, result),
        ))
    }

    /// Applies a declared function to its arguments.
    fn apply(&mut self, func: Func, args: Vec<Term>) -> PyResult<Term> {
        let func = func.resolve(self.epoch)?;
        let args = self.resolve_terms(&args)?;
        let id = self
            .arena
            .apply(func, &args)
            .map_err(|e| map_ir_error(&e))?;
        Ok(self.wrap(id))
    }

    // ---------------------------------------------------- uninterpreted sorts

    /// Declares an uninterpreted carrier sort (or returns the existing one).
    fn declare_uninterpreted_sort(&mut self, name: &str) -> SortRef {
        let sort = self.arena.declare_uninterpreted_sort(name);
        SortRef::new(self.epoch, sort)
    }

    /// The declared carrier sort of that name, or `None`.
    fn find_uninterpreted_sort(&self, name: &str) -> Option<SortRef> {
        self.arena
            .find_uninterpreted_sort(name)
            .map(|sort| SortRef::new(self.epoch, sort))
    }

    /// The name of a declared carrier sort.
    fn uninterpreted_sort_name(&self, sort: SortRef) -> PyResult<String> {
        let sort = sort.resolve(self.epoch)?;
        Ok(self.arena.uninterpreted_sort_name(sort).to_owned())
    }

    // ------------------------------------------------------------- datatypes

    /// Declares a datatype (constructors are added afterwards).
    fn declare_datatype(&mut self, name: &str) -> Datatype {
        Datatype::new(self.epoch, self.arena.declare_datatype(name))
    }

    /// Adds a constructor with `(field name, field sort)` pairs.
    fn add_constructor(
        &mut self,
        datatype: Datatype,
        name: &str,
        fields: Vec<(String, PySort)>,
    ) -> PyResult<Constructor> {
        let datatype = datatype.resolve(self.epoch)?;
        let fields: Vec<(String, Sort)> = fields
            .iter()
            .map(|(name, sort)| Ok((name.clone(), sort.resolve(self.epoch)?)))
            .collect::<PyResult<_>>()?;
        let constructor = self.arena.add_constructor(datatype, name, &fields);
        Ok(Constructor::new(self.epoch, constructor))
    }

    /// The constructors of a datatype, in declaration order.
    fn datatype_constructors(&self, datatype: Datatype) -> PyResult<Vec<Constructor>> {
        let datatype = datatype.resolve(self.epoch)?;
        Ok(self
            .arena
            .datatype_constructors(datatype)
            .iter()
            .map(|&c| Constructor::new(self.epoch, c))
            .collect())
    }

    /// The name of a constructor.
    fn constructor_name(&self, constructor: Constructor) -> PyResult<String> {
        let constructor = constructor.resolve(self.epoch)?;
        Ok(self.arena.constructor_name(constructor).to_owned())
    }

    /// The `(field name, field sort)` pairs of a constructor.
    fn constructor_fields(&self, constructor: Constructor) -> PyResult<Vec<(String, PySort)>> {
        let constructor = constructor.resolve(self.epoch)?;
        Ok(self
            .arena
            .constructor_fields(constructor)
            .iter()
            .map(|(name, sort)| (name.clone(), PySort::bound(self.epoch, *sort)))
            .collect())
    }

    /// Applies a constructor to its field values.
    fn construct(&mut self, constructor: Constructor, args: Vec<Term>) -> PyResult<Term> {
        let constructor = constructor.resolve(self.epoch)?;
        let args = self.resolve_terms(&args)?;
        let id = self
            .arena
            .construct(constructor, &args)
            .map_err(|e| map_ir_error(&e))?;
        Ok(self.wrap(id))
    }

    /// Selects field `index` of a value built by `constructor`.
    fn dt_select(&mut self, constructor: Constructor, index: u32, value: Term) -> PyResult<Term> {
        let constructor = constructor.resolve(self.epoch)?;
        let value = value.resolve(self.epoch)?;
        let id = self
            .arena
            .dt_select(constructor, index, value)
            .map_err(|e| map_ir_error(&e))?;
        Ok(self.wrap(id))
    }

    /// Tests whether a datatype value was built by `constructor`.
    fn dt_test(&mut self, constructor: Constructor, value: Term) -> PyResult<Term> {
        let constructor = constructor.resolve(self.epoch)?;
        let value = value.resolve(self.epoch)?;
        let id = self
            .arena
            .dt_test(constructor, value)
            .map_err(|e| map_ir_error(&e))?;
        Ok(self.wrap(id))
    }

    // ------------------------------------------------------------- constants

    /// The Boolean constant `true` or `false`.
    fn bool_const(&mut self, value: bool) -> Term {
        let id = self.arena.bool_const(value);
        self.wrap(id)
    }

    /// A bit-vector constant of `width` bits.
    ///
    /// `value` is an arbitrary-precision Python integer; widths above 128 use
    /// the wide representation. A negative `value` is rejected.
    fn bv_const(&mut self, width: u32, value: &Bound<'_, PyAny>) -> PyResult<Term> {
        let bits = python_int_to_lsb_bits(value, width)?;
        let id = if width <= 128 {
            let mut small: u128 = 0;
            for (index, bit) in bits.iter().enumerate() {
                if *bit {
                    small |= 1u128 << index;
                }
            }
            self.arena
                .bv_const(width, small)
                .map_err(|e| map_ir_error(&e))?
        } else {
            let value = axeyum_ir::lsb_bits_to_value(Sort::BitVec(width), &bits)
                .map_err(|e| map_ir_error(&e))?;
            let axeyum_ir::Value::WideBv(wide) = value else {
                return Err(AxeyumError::new_err(
                    "internal: wide bit-vector constant did not build a WideBv",
                ));
            };
            self.arena.wide_bv_const(wide)
        };
        Ok(self.wrap(id))
    }

    /// An integer constant (the evaluator's reference range is `i128`).
    fn int_const(&mut self, value: i128) -> Term {
        let id = self.arena.int_const(value);
        self.wrap(id)
    }

    /// A real constant `num / den`; `den` must be non-zero.
    fn real_ratio(&mut self, num: i128, den: i128) -> PyResult<Term> {
        let rational = Rational::checked_new(num, den).ok_or_else(|| {
            AxeyumError::new_err(format!("{num}/{den} is not a representable rational"))
        })?;
        let id = self.arena.real_const(rational);
        Ok(self.wrap(id))
    }

    /// A real constant equal to the integer `value`.
    fn real_const(&mut self, value: i128) -> Term {
        let id = self.arena.real_const(Rational::integer(value));
        self.wrap(id)
    }

    // ------------------------------------------------------- vars by name

    /// Declares (if needed) and reads a Boolean variable.
    fn bool_var(&mut self, name: &str) -> PyResult<Term> {
        let id = self.arena.bool_var(name).map_err(|e| map_ir_error(&e))?;
        Ok(self.wrap(id))
    }

    /// Declares (if needed) and reads a bit-vector variable.
    fn bv_var(&mut self, name: &str, width: u32) -> PyResult<Term> {
        let id = self
            .arena
            .bv_var(name, width)
            .map_err(|e| map_ir_error(&e))?;
        Ok(self.wrap(id))
    }

    /// Declares (if needed) and reads an integer variable.
    fn int_var(&mut self, name: &str) -> PyResult<Term> {
        let id = self.arena.int_var(name).map_err(|e| map_ir_error(&e))?;
        Ok(self.wrap(id))
    }

    /// Declares (if needed) and reads a real variable.
    fn real_var(&mut self, name: &str) -> PyResult<Term> {
        let id = self.arena.real_var(name).map_err(|e| map_ir_error(&e))?;
        Ok(self.wrap(id))
    }

    /// Declares (if needed) and reads a bit-vector-indexed array variable.
    fn array_var(&mut self, name: &str, index: u32, element: u32) -> PyResult<Term> {
        let id = self
            .arena
            .array_var(name, index, element)
            .map_err(|e| map_ir_error(&e))?;
        Ok(self.wrap(id))
    }

    // ---- generated builders (see the module docs for totality) ----
    /// `not_` over one operand.
    fn not_(&mut self, a: Term) -> PyResult<Term> {
        let a = a.resolve(self.epoch)?;
        let id = self.arena.not(a).map_err(|e| map_ir_error(&e))?;
        Ok(self.wrap(id))
    }

    /// `bvneg` over one operand.
    fn bvneg(&mut self, a: Term) -> PyResult<Term> {
        let a = a.resolve(self.epoch)?;
        let id = self.arena.bv_neg(a).map_err(|e| map_ir_error(&e))?;
        Ok(self.wrap(id))
    }

    /// `bvnot` over one operand.
    fn bvnot(&mut self, a: Term) -> PyResult<Term> {
        let a = a.resolve(self.epoch)?;
        let id = self.arena.bv_not(a).map_err(|e| map_ir_error(&e))?;
        Ok(self.wrap(id))
    }

    /// `int_neg` over one operand.
    fn int_neg(&mut self, a: Term) -> PyResult<Term> {
        let a = a.resolve(self.epoch)?;
        let id = self.arena.int_neg(a).map_err(|e| map_ir_error(&e))?;
        Ok(self.wrap(id))
    }

    /// `int_abs` over one operand.
    fn int_abs(&mut self, a: Term) -> PyResult<Term> {
        let a = a.resolve(self.epoch)?;
        let id = self.arena.int_abs(a).map_err(|e| map_ir_error(&e))?;
        Ok(self.wrap(id))
    }

    /// cvc5's total `pow2`: `2**x` for `x >= 0`, and the DEFINED value `0` for `x < 0`.
    fn int_pow2(&mut self, a: Term) -> PyResult<Term> {
        let a = a.resolve(self.epoch)?;
        let id = self.arena.int_pow2(a).map_err(|e| map_ir_error(&e))?;
        Ok(self.wrap(id))
    }

    /// `real_neg` over one operand.
    fn real_neg(&mut self, a: Term) -> PyResult<Term> {
        let a = a.resolve(self.epoch)?;
        let id = self.arena.real_neg(a).map_err(|e| map_ir_error(&e))?;
        Ok(self.wrap(id))
    }

    /// `to_real`: the exact `Int -> Real` embedding.
    #[allow(clippy::wrong_self_convention)]
    fn to_real(&mut self, a: Term) -> PyResult<Term> {
        let a = a.resolve(self.epoch)?;
        let id = self.arena.int_to_real(a).map_err(|e| map_ir_error(&e))?;
        Ok(self.wrap(id))
    }

    /// `to_int`: the floor of a real, as an integer.
    #[allow(clippy::wrong_self_convention)]
    fn to_int(&mut self, a: Term) -> PyResult<Term> {
        let a = a.resolve(self.epoch)?;
        let id = self.arena.real_to_int(a).map_err(|e| map_ir_error(&e))?;
        Ok(self.wrap(id))
    }

    /// `is_int` over one operand.
    fn is_int(&mut self, a: Term) -> PyResult<Term> {
        let a = a.resolve(self.epoch)?;
        let id = self.arena.real_is_int(a).map_err(|e| map_ir_error(&e))?;
        Ok(self.wrap(id))
    }

    /// `bv2nat` over one operand.
    fn bv2nat(&mut self, a: Term) -> PyResult<Term> {
        let a = a.resolve(self.epoch)?;
        let id = self.arena.bv2nat(a).map_err(|e| map_ir_error(&e))?;
        Ok(self.wrap(id))
    }

    /// `seq_len` over one operand.
    fn seq_len(&mut self, a: Term) -> PyResult<Term> {
        let a = a.resolve(self.epoch)?;
        let id = self.arena.seq_len(a).map_err(|e| map_ir_error(&e))?;
        Ok(self.wrap(id))
    }

    /// `seq_unit` over one operand.
    fn seq_unit(&mut self, a: Term) -> PyResult<Term> {
        let a = a.resolve(self.epoch)?;
        let id = self.arena.seq_unit(a).map_err(|e| map_ir_error(&e))?;
        Ok(self.wrap(id))
    }

    /// `rounding_mode_from_bits` over one operand.
    fn rounding_mode_from_bits(&mut self, a: Term) -> PyResult<Term> {
        let a = a.resolve(self.epoch)?;
        let id = self
            .arena
            .rounding_mode_from_bits(a)
            .map_err(|e| map_ir_error(&e))?;
        Ok(self.wrap(id))
    }

    /// `and_` over two operands.
    fn and_(&mut self, a: Term, b: Term) -> PyResult<Term> {
        let a = a.resolve(self.epoch)?;
        let b = b.resolve(self.epoch)?;
        let id = self.arena.and(a, b).map_err(|e| map_ir_error(&e))?;
        Ok(self.wrap(id))
    }

    /// `or_` over two operands.
    fn or_(&mut self, a: Term, b: Term) -> PyResult<Term> {
        let a = a.resolve(self.epoch)?;
        let b = b.resolve(self.epoch)?;
        let id = self.arena.or(a, b).map_err(|e| map_ir_error(&e))?;
        Ok(self.wrap(id))
    }

    /// `xor_` over two operands.
    fn xor_(&mut self, a: Term, b: Term) -> PyResult<Term> {
        let a = a.resolve(self.epoch)?;
        let b = b.resolve(self.epoch)?;
        let id = self.arena.xor(a, b).map_err(|e| map_ir_error(&e))?;
        Ok(self.wrap(id))
    }

    /// `implies` over two operands.
    fn implies(&mut self, a: Term, b: Term) -> PyResult<Term> {
        let a = a.resolve(self.epoch)?;
        let b = b.resolve(self.epoch)?;
        let id = self.arena.implies(a, b).map_err(|e| map_ir_error(&e))?;
        Ok(self.wrap(id))
    }

    /// `eq` over two operands.
    fn eq(&mut self, a: Term, b: Term) -> PyResult<Term> {
        let a = a.resolve(self.epoch)?;
        let b = b.resolve(self.epoch)?;
        let id = self.arena.eq(a, b).map_err(|e| map_ir_error(&e))?;
        Ok(self.wrap(id))
    }

    /// `bvand` over two operands.
    fn bvand(&mut self, a: Term, b: Term) -> PyResult<Term> {
        let a = a.resolve(self.epoch)?;
        let b = b.resolve(self.epoch)?;
        let id = self.arena.bv_and(a, b).map_err(|e| map_ir_error(&e))?;
        Ok(self.wrap(id))
    }

    /// `bvor` over two operands.
    fn bvor(&mut self, a: Term, b: Term) -> PyResult<Term> {
        let a = a.resolve(self.epoch)?;
        let b = b.resolve(self.epoch)?;
        let id = self.arena.bv_or(a, b).map_err(|e| map_ir_error(&e))?;
        Ok(self.wrap(id))
    }

    /// `bvxor` over two operands.
    fn bvxor(&mut self, a: Term, b: Term) -> PyResult<Term> {
        let a = a.resolve(self.epoch)?;
        let b = b.resolve(self.epoch)?;
        let id = self.arena.bv_xor(a, b).map_err(|e| map_ir_error(&e))?;
        Ok(self.wrap(id))
    }

    /// `bvnand` over two operands.
    fn bvnand(&mut self, a: Term, b: Term) -> PyResult<Term> {
        let a = a.resolve(self.epoch)?;
        let b = b.resolve(self.epoch)?;
        let id = self.arena.bv_nand(a, b).map_err(|e| map_ir_error(&e))?;
        Ok(self.wrap(id))
    }

    /// `bvnor` over two operands.
    fn bvnor(&mut self, a: Term, b: Term) -> PyResult<Term> {
        let a = a.resolve(self.epoch)?;
        let b = b.resolve(self.epoch)?;
        let id = self.arena.bv_nor(a, b).map_err(|e| map_ir_error(&e))?;
        Ok(self.wrap(id))
    }

    /// `bvxnor` over two operands.
    fn bvxnor(&mut self, a: Term, b: Term) -> PyResult<Term> {
        let a = a.resolve(self.epoch)?;
        let b = b.resolve(self.epoch)?;
        let id = self.arena.bv_xnor(a, b).map_err(|e| map_ir_error(&e))?;
        Ok(self.wrap(id))
    }

    /// `bvadd` over two operands.
    fn bvadd(&mut self, a: Term, b: Term) -> PyResult<Term> {
        let a = a.resolve(self.epoch)?;
        let b = b.resolve(self.epoch)?;
        let id = self.arena.bv_add(a, b).map_err(|e| map_ir_error(&e))?;
        Ok(self.wrap(id))
    }

    /// `bvsub` over two operands.
    fn bvsub(&mut self, a: Term, b: Term) -> PyResult<Term> {
        let a = a.resolve(self.epoch)?;
        let b = b.resolve(self.epoch)?;
        let id = self.arena.bv_sub(a, b).map_err(|e| map_ir_error(&e))?;
        Ok(self.wrap(id))
    }

    /// `bvmul` over two operands.
    fn bvmul(&mut self, a: Term, b: Term) -> PyResult<Term> {
        let a = a.resolve(self.epoch)?;
        let b = b.resolve(self.epoch)?;
        let id = self.arena.bv_mul(a, b).map_err(|e| map_ir_error(&e))?;
        Ok(self.wrap(id))
    }

    /// Unsigned division. **Total**: `bvudiv(x, 0)` is all-ones, not an error.
    fn bvudiv(&mut self, a: Term, b: Term) -> PyResult<Term> {
        let a = a.resolve(self.epoch)?;
        let b = b.resolve(self.epoch)?;
        let id = self.arena.bv_udiv(a, b).map_err(|e| map_ir_error(&e))?;
        Ok(self.wrap(id))
    }

    /// Unsigned remainder. **Total**: `bvurem(x, 0)` is `x`, not an error.
    fn bvurem(&mut self, a: Term, b: Term) -> PyResult<Term> {
        let a = a.resolve(self.epoch)?;
        let b = b.resolve(self.epoch)?;
        let id = self.arena.bv_urem(a, b).map_err(|e| map_ir_error(&e))?;
        Ok(self.wrap(id))
    }

    /// Signed division. **Total**: by zero it is `-1` for a non-negative dividend and `1` otherwise.
    fn bvsdiv(&mut self, a: Term, b: Term) -> PyResult<Term> {
        let a = a.resolve(self.epoch)?;
        let b = b.resolve(self.epoch)?;
        let id = self.arena.bv_sdiv(a, b).map_err(|e| map_ir_error(&e))?;
        Ok(self.wrap(id))
    }

    /// Signed remainder. **Total**: `bvsrem(x, 0)` is `x`.
    fn bvsrem(&mut self, a: Term, b: Term) -> PyResult<Term> {
        let a = a.resolve(self.epoch)?;
        let b = b.resolve(self.epoch)?;
        let id = self.arena.bv_srem(a, b).map_err(|e| map_ir_error(&e))?;
        Ok(self.wrap(id))
    }

    /// Signed modulo. **Total**: `bvsmod(x, 0)` is `x`.
    fn bvsmod(&mut self, a: Term, b: Term) -> PyResult<Term> {
        let a = a.resolve(self.epoch)?;
        let b = b.resolve(self.epoch)?;
        let id = self.arena.bv_smod(a, b).map_err(|e| map_ir_error(&e))?;
        Ok(self.wrap(id))
    }

    /// Logical left shift; amounts `>= width` yield zero.
    fn bvshl(&mut self, a: Term, b: Term) -> PyResult<Term> {
        let a = a.resolve(self.epoch)?;
        let b = b.resolve(self.epoch)?;
        let id = self.arena.bv_shl(a, b).map_err(|e| map_ir_error(&e))?;
        Ok(self.wrap(id))
    }

    /// Logical right shift; amounts `>= width` yield zero.
    fn bvlshr(&mut self, a: Term, b: Term) -> PyResult<Term> {
        let a = a.resolve(self.epoch)?;
        let b = b.resolve(self.epoch)?;
        let id = self.arena.bv_lshr(a, b).map_err(|e| map_ir_error(&e))?;
        Ok(self.wrap(id))
    }

    /// Arithmetic right shift; amounts `>= width` yield all sign bits.
    fn bvashr(&mut self, a: Term, b: Term) -> PyResult<Term> {
        let a = a.resolve(self.epoch)?;
        let b = b.resolve(self.epoch)?;
        let id = self.arena.bv_ashr(a, b).map_err(|e| map_ir_error(&e))?;
        Ok(self.wrap(id))
    }

    /// `bvult` over two operands.
    fn bvult(&mut self, a: Term, b: Term) -> PyResult<Term> {
        let a = a.resolve(self.epoch)?;
        let b = b.resolve(self.epoch)?;
        let id = self.arena.bv_ult(a, b).map_err(|e| map_ir_error(&e))?;
        Ok(self.wrap(id))
    }

    /// `bvule` over two operands.
    fn bvule(&mut self, a: Term, b: Term) -> PyResult<Term> {
        let a = a.resolve(self.epoch)?;
        let b = b.resolve(self.epoch)?;
        let id = self.arena.bv_ule(a, b).map_err(|e| map_ir_error(&e))?;
        Ok(self.wrap(id))
    }

    /// `bvugt` over two operands.
    fn bvugt(&mut self, a: Term, b: Term) -> PyResult<Term> {
        let a = a.resolve(self.epoch)?;
        let b = b.resolve(self.epoch)?;
        let id = self.arena.bv_ugt(a, b).map_err(|e| map_ir_error(&e))?;
        Ok(self.wrap(id))
    }

    /// `bvuge` over two operands.
    fn bvuge(&mut self, a: Term, b: Term) -> PyResult<Term> {
        let a = a.resolve(self.epoch)?;
        let b = b.resolve(self.epoch)?;
        let id = self.arena.bv_uge(a, b).map_err(|e| map_ir_error(&e))?;
        Ok(self.wrap(id))
    }

    /// `bvslt` over two operands.
    fn bvslt(&mut self, a: Term, b: Term) -> PyResult<Term> {
        let a = a.resolve(self.epoch)?;
        let b = b.resolve(self.epoch)?;
        let id = self.arena.bv_slt(a, b).map_err(|e| map_ir_error(&e))?;
        Ok(self.wrap(id))
    }

    /// `bvsle` over two operands.
    fn bvsle(&mut self, a: Term, b: Term) -> PyResult<Term> {
        let a = a.resolve(self.epoch)?;
        let b = b.resolve(self.epoch)?;
        let id = self.arena.bv_sle(a, b).map_err(|e| map_ir_error(&e))?;
        Ok(self.wrap(id))
    }

    /// `bvsgt` over two operands.
    fn bvsgt(&mut self, a: Term, b: Term) -> PyResult<Term> {
        let a = a.resolve(self.epoch)?;
        let b = b.resolve(self.epoch)?;
        let id = self.arena.bv_sgt(a, b).map_err(|e| map_ir_error(&e))?;
        Ok(self.wrap(id))
    }

    /// `bvsge` over two operands.
    fn bvsge(&mut self, a: Term, b: Term) -> PyResult<Term> {
        let a = a.resolve(self.epoch)?;
        let b = b.resolve(self.epoch)?;
        let id = self.arena.bv_sge(a, b).map_err(|e| map_ir_error(&e))?;
        Ok(self.wrap(id))
    }

    /// `bvcomp` over two operands.
    fn bvcomp(&mut self, a: Term, b: Term) -> PyResult<Term> {
        let a = a.resolve(self.epoch)?;
        let b = b.resolve(self.epoch)?;
        let id = self.arena.bv_comp(a, b).map_err(|e| map_ir_error(&e))?;
        Ok(self.wrap(id))
    }

    /// `bvuaddo` over two operands.
    fn bvuaddo(&mut self, a: Term, b: Term) -> PyResult<Term> {
        let a = a.resolve(self.epoch)?;
        let b = b.resolve(self.epoch)?;
        let id = self.arena.bv_uaddo(a, b).map_err(|e| map_ir_error(&e))?;
        Ok(self.wrap(id))
    }

    /// `bvsaddo` over two operands.
    fn bvsaddo(&mut self, a: Term, b: Term) -> PyResult<Term> {
        let a = a.resolve(self.epoch)?;
        let b = b.resolve(self.epoch)?;
        let id = self.arena.bv_saddo(a, b).map_err(|e| map_ir_error(&e))?;
        Ok(self.wrap(id))
    }

    /// `bvusubo` over two operands.
    fn bvusubo(&mut self, a: Term, b: Term) -> PyResult<Term> {
        let a = a.resolve(self.epoch)?;
        let b = b.resolve(self.epoch)?;
        let id = self.arena.bv_usubo(a, b).map_err(|e| map_ir_error(&e))?;
        Ok(self.wrap(id))
    }

    /// `bvssubo` over two operands.
    fn bvssubo(&mut self, a: Term, b: Term) -> PyResult<Term> {
        let a = a.resolve(self.epoch)?;
        let b = b.resolve(self.epoch)?;
        let id = self.arena.bv_ssubo(a, b).map_err(|e| map_ir_error(&e))?;
        Ok(self.wrap(id))
    }

    /// `bvumulo` over two operands.
    fn bvumulo(&mut self, a: Term, b: Term) -> PyResult<Term> {
        let a = a.resolve(self.epoch)?;
        let b = b.resolve(self.epoch)?;
        let id = self.arena.bv_umulo(a, b).map_err(|e| map_ir_error(&e))?;
        Ok(self.wrap(id))
    }

    /// `bvsmulo` over two operands.
    fn bvsmulo(&mut self, a: Term, b: Term) -> PyResult<Term> {
        let a = a.resolve(self.epoch)?;
        let b = b.resolve(self.epoch)?;
        let id = self.arena.bv_smulo(a, b).map_err(|e| map_ir_error(&e))?;
        Ok(self.wrap(id))
    }

    /// `concat` over two operands.
    fn concat(&mut self, a: Term, b: Term) -> PyResult<Term> {
        let a = a.resolve(self.epoch)?;
        let b = b.resolve(self.epoch)?;
        let id = self.arena.concat(a, b).map_err(|e| map_ir_error(&e))?;
        Ok(self.wrap(id))
    }

    /// `int_add` over two operands.
    fn int_add(&mut self, a: Term, b: Term) -> PyResult<Term> {
        let a = a.resolve(self.epoch)?;
        let b = b.resolve(self.epoch)?;
        let id = self.arena.int_add(a, b).map_err(|e| map_ir_error(&e))?;
        Ok(self.wrap(id))
    }

    /// `int_sub` over two operands.
    fn int_sub(&mut self, a: Term, b: Term) -> PyResult<Term> {
        let a = a.resolve(self.epoch)?;
        let b = b.resolve(self.epoch)?;
        let id = self.arena.int_sub(a, b).map_err(|e| map_ir_error(&e))?;
        Ok(self.wrap(id))
    }

    /// `int_mul` over two operands.
    fn int_mul(&mut self, a: Term, b: Term) -> PyResult<Term> {
        let a = a.resolve(self.epoch)?;
        let b = b.resolve(self.epoch)?;
        let id = self.arena.int_mul(a, b).map_err(|e| map_ir_error(&e))?;
        Ok(self.wrap(id))
    }

    /// SMT-LIB integer `div`. **Total**: `int_div(a, 0)` is `0` by the in-tree convention.
    fn int_div(&mut self, a: Term, b: Term) -> PyResult<Term> {
        let a = a.resolve(self.epoch)?;
        let b = b.resolve(self.epoch)?;
        let id = self.arena.int_div(a, b).map_err(|e| map_ir_error(&e))?;
        Ok(self.wrap(id))
    }

    /// SMT-LIB integer `mod`. **Total**: `int_mod(a, 0)` is `a` by the in-tree convention.
    fn int_mod(&mut self, a: Term, b: Term) -> PyResult<Term> {
        let a = a.resolve(self.epoch)?;
        let b = b.resolve(self.epoch)?;
        let id = self.arena.int_mod(a, b).map_err(|e| map_ir_error(&e))?;
        Ok(self.wrap(id))
    }

    /// `int_lt` over two operands.
    fn int_lt(&mut self, a: Term, b: Term) -> PyResult<Term> {
        let a = a.resolve(self.epoch)?;
        let b = b.resolve(self.epoch)?;
        let id = self.arena.int_lt(a, b).map_err(|e| map_ir_error(&e))?;
        Ok(self.wrap(id))
    }

    /// `int_le` over two operands.
    fn int_le(&mut self, a: Term, b: Term) -> PyResult<Term> {
        let a = a.resolve(self.epoch)?;
        let b = b.resolve(self.epoch)?;
        let id = self.arena.int_le(a, b).map_err(|e| map_ir_error(&e))?;
        Ok(self.wrap(id))
    }

    /// `int_gt` over two operands.
    fn int_gt(&mut self, a: Term, b: Term) -> PyResult<Term> {
        let a = a.resolve(self.epoch)?;
        let b = b.resolve(self.epoch)?;
        let id = self.arena.int_gt(a, b).map_err(|e| map_ir_error(&e))?;
        Ok(self.wrap(id))
    }

    /// `int_ge` over two operands.
    fn int_ge(&mut self, a: Term, b: Term) -> PyResult<Term> {
        let a = a.resolve(self.epoch)?;
        let b = b.resolve(self.epoch)?;
        let id = self.arena.int_ge(a, b).map_err(|e| map_ir_error(&e))?;
        Ok(self.wrap(id))
    }

    /// `real_add` over two operands.
    fn real_add(&mut self, a: Term, b: Term) -> PyResult<Term> {
        let a = a.resolve(self.epoch)?;
        let b = b.resolve(self.epoch)?;
        let id = self.arena.real_add(a, b).map_err(|e| map_ir_error(&e))?;
        Ok(self.wrap(id))
    }

    /// `real_sub` over two operands.
    fn real_sub(&mut self, a: Term, b: Term) -> PyResult<Term> {
        let a = a.resolve(self.epoch)?;
        let b = b.resolve(self.epoch)?;
        let id = self.arena.real_sub(a, b).map_err(|e| map_ir_error(&e))?;
        Ok(self.wrap(id))
    }

    /// `real_mul` over two operands.
    fn real_mul(&mut self, a: Term, b: Term) -> PyResult<Term> {
        let a = a.resolve(self.epoch)?;
        let b = b.resolve(self.epoch)?;
        let id = self.arena.real_mul(a, b).map_err(|e| map_ir_error(&e))?;
        Ok(self.wrap(id))
    }

    /// Real `/`. **Total**: the ground evaluator uses `x / 0 = 0`.
    fn real_div(&mut self, a: Term, b: Term) -> PyResult<Term> {
        let a = a.resolve(self.epoch)?;
        let b = b.resolve(self.epoch)?;
        let id = self.arena.real_div(a, b).map_err(|e| map_ir_error(&e))?;
        Ok(self.wrap(id))
    }

    /// `real_lt` over two operands.
    fn real_lt(&mut self, a: Term, b: Term) -> PyResult<Term> {
        let a = a.resolve(self.epoch)?;
        let b = b.resolve(self.epoch)?;
        let id = self.arena.real_lt(a, b).map_err(|e| map_ir_error(&e))?;
        Ok(self.wrap(id))
    }

    /// `real_le` over two operands.
    fn real_le(&mut self, a: Term, b: Term) -> PyResult<Term> {
        let a = a.resolve(self.epoch)?;
        let b = b.resolve(self.epoch)?;
        let id = self.arena.real_le(a, b).map_err(|e| map_ir_error(&e))?;
        Ok(self.wrap(id))
    }

    /// `real_gt` over two operands.
    fn real_gt(&mut self, a: Term, b: Term) -> PyResult<Term> {
        let a = a.resolve(self.epoch)?;
        let b = b.resolve(self.epoch)?;
        let id = self.arena.real_gt(a, b).map_err(|e| map_ir_error(&e))?;
        Ok(self.wrap(id))
    }

    /// `real_ge` over two operands.
    fn real_ge(&mut self, a: Term, b: Term) -> PyResult<Term> {
        let a = a.resolve(self.epoch)?;
        let b = b.resolve(self.epoch)?;
        let id = self.arena.real_ge(a, b).map_err(|e| map_ir_error(&e))?;
        Ok(self.wrap(id))
    }

    /// `select` over two operands.
    fn select(&mut self, a: Term, b: Term) -> PyResult<Term> {
        let a = a.resolve(self.epoch)?;
        let b = b.resolve(self.epoch)?;
        let id = self.arena.select(a, b).map_err(|e| map_ir_error(&e))?;
        Ok(self.wrap(id))
    }

    /// `seq_concat` over two operands.
    fn seq_concat(&mut self, a: Term, b: Term) -> PyResult<Term> {
        let a = a.resolve(self.epoch)?;
        let b = b.resolve(self.epoch)?;
        let id = self.arena.seq_concat(a, b).map_err(|e| map_ir_error(&e))?;
        Ok(self.wrap(id))
    }

    /// `zero_extend` with a constant parameter.
    fn zero_extend(&mut self, by: u32, a: Term) -> PyResult<Term> {
        let a = a.resolve(self.epoch)?;
        let id = self.arena.zero_ext(by, a).map_err(|e| map_ir_error(&e))?;
        Ok(self.wrap(id))
    }

    /// `sign_extend` with a constant parameter.
    fn sign_extend(&mut self, by: u32, a: Term) -> PyResult<Term> {
        let a = a.resolve(self.epoch)?;
        let id = self.arena.sign_ext(by, a).map_err(|e| map_ir_error(&e))?;
        Ok(self.wrap(id))
    }

    /// Rotate left, normalized modulo the operand width at build time.
    fn rotate_left(&mut self, by: u32, a: Term) -> PyResult<Term> {
        let a = a.resolve(self.epoch)?;
        let id = self
            .arena
            .rotate_left(by, a)
            .map_err(|e| map_ir_error(&e))?;
        Ok(self.wrap(id))
    }

    /// Rotate right, normalized modulo the operand width at build time.
    fn rotate_right(&mut self, by: u32, a: Term) -> PyResult<Term> {
        let a = a.resolve(self.epoch)?;
        let id = self
            .arena
            .rotate_right(by, a)
            .map_err(|e| map_ir_error(&e))?;
        Ok(self.wrap(id))
    }

    /// `repeat` with a constant parameter.
    fn repeat(&mut self, by: u32, a: Term) -> PyResult<Term> {
        let a = a.resolve(self.epoch)?;
        let id = self.arena.bv_repeat(by, a).map_err(|e| map_ir_error(&e))?;
        Ok(self.wrap(id))
    }

    /// `int2bv` with a constant parameter.
    fn int2bv(&mut self, by: u32, a: Term) -> PyResult<Term> {
        let a = a.resolve(self.epoch)?;
        let id = self.arena.int2bv(by, a).map_err(|e| map_ir_error(&e))?;
        Ok(self.wrap(id))
    }

    /// Two's-complement negation-overflow predicate.
    fn bvnego(&mut self, a: Term) -> PyResult<Term> {
        let a = a.resolve(self.epoch)?;
        let id = self.arena.bv_nego(a).map_err(|e| map_ir_error(&e))?;
        Ok(self.wrap(id))
    }

    /// If-then-else over a Boolean condition and same-sorted branches.
    fn ite(&mut self, condition: Term, then_: Term, else_: Term) -> PyResult<Term> {
        let condition = condition.resolve(self.epoch)?;
        let then_ = then_.resolve(self.epoch)?;
        let else_ = else_.resolve(self.epoch)?;
        let id = self
            .arena
            .ite(condition, then_, else_)
            .map_err(|e| map_ir_error(&e))?;
        Ok(self.wrap(id))
    }

    /// Bit slice `[hi:lo]`, inclusive; the result is `hi - lo + 1` bits.
    fn extract(&mut self, hi: u32, lo: u32, a: Term) -> PyResult<Term> {
        let a = a.resolve(self.epoch)?;
        let id = self
            .arena
            .extract(hi, lo, a)
            .map_err(|e| map_ir_error(&e))?;
        Ok(self.wrap(id))
    }

    /// Zero-extends or truncates `a` to exactly `width` bits.
    fn coerce_to(&mut self, a: Term, width: u32) -> PyResult<Term> {
        let a = a.resolve(self.epoch)?;
        let id = self
            .arena
            .coerce_to(a, width)
            .map_err(|e| map_ir_error(&e))?;
        Ok(self.wrap(id))
    }

    /// `x mod n == 0` for a constant `n`.
    fn int_divisible(&mut self, x: Term, n: i128) -> PyResult<Term> {
        let x = x.resolve(self.epoch)?;
        let id = self
            .arena
            .int_divisible(x, n)
            .map_err(|e| map_ir_error(&e))?;
        Ok(self.wrap(id))
    }

    /// Array write `store(array, index, element)`.
    fn store(&mut self, array: Term, index: Term, element: Term) -> PyResult<Term> {
        let array = array.resolve(self.epoch)?;
        let index = index.resolve(self.epoch)?;
        let element = element.resolve(self.epoch)?;
        let id = self
            .arena
            .store(array, index, element)
            .map_err(|e| map_ir_error(&e))?;
        Ok(self.wrap(id))
    }

    /// The constant array over a `BitVec(index)` index mapping everything to
    /// `value`.
    fn const_array(&mut self, index: u32, value: Term) -> PyResult<Term> {
        let value = value.resolve(self.epoch)?;
        let id = self
            .arena
            .const_array(index, value)
            .map_err(|e| map_ir_error(&e))?;
        Ok(self.wrap(id))
    }

    /// The empty sequence of the given element sort.
    fn seq_empty(&mut self, element: &PySort) -> PyResult<Term> {
        let element = element.resolve(self.epoch)?;
        let key = axeyum_ir::ArraySortKey::from_sort(element)
            .ok_or_else(|| map_ir_error(&IrError::Unsupported("nested sequences are deferred")))?;
        let id = self.arena.seq_empty(key);
        Ok(self.wrap(id))
    }

    /// Reinterprets a `BitVec(exp + sig)` operand as a float of that format.
    fn fp_from_bits(&mut self, x: Term, exp: u32, sig: u32) -> PyResult<Term> {
        let x = x.resolve(self.epoch)?;
        let id = self
            .arena
            .fp_from_bits(x, exp, sig)
            .map_err(|e| map_ir_error(&e))?;
        Ok(self.wrap(id))
    }

    // ------------------------------------------------------------ quantifiers

    /// `(forall ((var S)) body)`.
    fn forall(&mut self, var: Symbol, body: Term) -> PyResult<Term> {
        let var = var.resolve(self.epoch)?;
        let body = body.resolve(self.epoch)?;
        let id = self.arena.forall(var, body).map_err(|e| map_ir_error(&e))?;
        Ok(self.wrap(id))
    }

    /// `(exists ((var S)) body)`.
    fn exists(&mut self, var: Symbol, body: Term) -> PyResult<Term> {
        let var = var.resolve(self.epoch)?;
        let body = body.resolve(self.epoch)?;
        let id = self.arena.exists(var, body).map_err(|e| map_ir_error(&e))?;
        Ok(self.wrap(id))
    }

    /// Attaches `:pattern` groups to a quantifier term.
    fn set_quantifier_patterns(
        &mut self,
        quantifier: Term,
        groups: Vec<Vec<Term>>,
    ) -> PyResult<()> {
        let quantifier = quantifier.resolve(self.epoch)?;
        let groups: Vec<Vec<TermId>> = groups
            .iter()
            .map(|group| self.resolve_terms(group))
            .collect::<PyResult<_>>()?;
        self.arena.set_quantifier_patterns(quantifier, groups);
        Ok(())
    }

    /// The `:pattern` groups of a quantifier term, or `None`.
    fn quantifier_patterns(&self, quantifier: Term) -> PyResult<Option<Vec<Vec<Term>>>> {
        let quantifier = quantifier.resolve(self.epoch)?;
        Ok(self.arena.quantifier_patterns(quantifier).map(|groups| {
            groups
                .iter()
                .map(|group| group.iter().map(|&t| Term::new(self.epoch, t)).collect())
                .collect()
        }))
    }

    // --------------------------------------------------------- introspection

    /// The structural node of `term`, copied out of the arena.
    fn node(&self, py: Python<'_>, term: Term) -> PyResult<PyTermNode> {
        let id = term.resolve(self.epoch)?;
        PyTermNode::build(py, self.epoch, self.arena.node(id))
    }

    /// The sort of `term`.
    fn sort_of(&self, term: Term) -> PyResult<PySort> {
        let id = term.resolve(self.epoch)?;
        Ok(PySort::bound(self.epoch, self.arena.sort_of(id)))
    }

    /// Rebuilds `term`'s operator over new arguments (structural rewriting).
    fn rebuild_with_args(&mut self, term: Term, args: Vec<Term>) -> PyResult<Term> {
        let id = term.resolve(self.epoch)?;
        let args = self.resolve_terms(&args)?;
        let rebuilt = self.arena.rebuild_with_args(id, &args);
        Ok(self.wrap(rebuilt))
    }

    /// Renders `term` as SMT-LIB-flavoured text.
    ///
    /// This is `axeyum_ir::render`, the IR's only term-to-text path. It lives
    /// on the arena rather than on `Term.__str__` because a `Term` is a bare
    /// `(epoch, index)` pair and does not hold the arena that gives it meaning.
    fn render(&self, term: Term) -> PyResult<String> {
        let id = term.resolve(self.epoch)?;
        Ok(axeyum_ir::render(&self.arena, id))
    }

    /// Structural statistics over `roots`.
    fn term_stats(&self, roots: Vec<Term>) -> PyResult<PyTermStats> {
        let roots = self.resolve_terms(&roots)?;
        Ok(PyTermStats::new(axeyum_ir::TermStats::compute(
            &self.arena,
            &roots,
        )))
    }

    /// A sharing-preserving SMT-LIB script asserting every term in `assertions`.
    ///
    /// Terms with fan-in above one are hoisted to 0-ary `define-fun`s, so the
    /// output is linear in the DAG rather than in the tree.
    fn write_script(&self, assertions: Vec<Term>) -> PyResult<String> {
        let assertions = self.resolve_terms(&assertions)?;
        Ok(axeyum_smtlib::write_script(&self.arena, &assertions))
    }

    /// A fresh, empty assignment bound to this arena.
    fn assignment(&self) -> crate::ir::evaluate::PyAssignment {
        crate::ir::evaluate::PyAssignment::empty(self.epoch)
    }
}

/// The LSB-first bits of a non-negative Python integer, at `width` bits.
pub(crate) fn python_int_to_lsb_bits(value: &Bound<'_, PyAny>, width: u32) -> PyResult<Vec<bool>> {
    if width == 0 || width > axeyum_ir::MAX_BV_WIDTH {
        return Err(map_ir_error(&IrError::InvalidWidth(width)));
    }
    let integer = value.cast::<PyInt>().map_err(|_| {
        crate::ir::types::SortError::new_err("a bit-vector constant needs a Python int")
    })?;
    if integer.lt(0i64)? {
        return Err(crate::ir::types::SortError::new_err(
            "a bit-vector constant is an UNSIGNED value; negate it with bvneg instead",
        ));
    }
    let byte_len = (width as usize).div_ceil(8);
    let bytes: Vec<u8> = integer
        .call_method1("to_bytes", (byte_len, "little"))
        .map_err(|_| {
            crate::ir::types::SortError::new_err(format!("constant does not fit in {width} bits"))
        })?
        .extract()?;
    let mut bits = vec![false; width as usize];
    for (index, bit) in bits.iter_mut().enumerate() {
        *bit = bytes[index / 8] & (1 << (index % 8)) != 0;
    }
    // Anything above `width` in the last byte would silently truncate.
    let leftover = (byte_len * 8) - width as usize;
    if leftover > 0 && bytes[byte_len - 1] >> (8 - leftover) != 0 {
        return Err(crate::ir::types::SortError::new_err(format!(
            "constant does not fit in {width} bits"
        )));
    }
    Ok(bits)
}

#[cfg(test)]
mod tests {
    use axeyum_ir::Sort;
    use pyo3::Python;

    use super::Arena;
    use crate::ir::types::{EpochError, PySort, Term};

    /// Every arena gets its own epoch, and epochs never repeat.
    ///
    /// This is the whole basis of the handle invariant: two arenas sharing an
    /// epoch would accept each other's `Term`s, and a `TermId` is a dense index
    /// -- so the call would silently denote a DIFFERENT term rather than fail.
    #[test]
    fn arena_epochs_are_monotone_and_distinct() {
        let first = Arena::new();
        let second = Arena::new();
        let third = Arena::new();
        assert!(first.epoch < second.epoch, "epochs must increase");
        assert!(second.epoch < third.epoch, "epochs must increase");
        // Never zero: `PySort` uses epoch 0 for the arena-independent sorts and
        // skips the check for them, so an arena at epoch 0 would disable it.
        assert!(first.epoch >= 1);
    }

    /// A `Term` minted by one arena is refused by another, as `EpochError`.
    #[test]
    fn a_term_from_another_arena_is_an_epoch_error() {
        Python::attach(|py| {
            let mut origin = Arena::new();
            let other = Arena::new();
            let sort = PySort::universal(Sort::Bool);
            let symbol = origin.declare("p", &sort).expect("declare p");
            let term: Term = origin.var(symbol).expect("var p");

            // Same arena: fine.
            term.resolve(origin.epoch)
                .expect("its own arena accepts it");

            let error = term
                .resolve(other.epoch)
                .expect_err("another arena must refuse it");
            assert!(
                error.is_instance_of::<EpochError>(py),
                "expected EpochError, got {error}"
            );
            let message = error.to_string();
            assert!(
                message.contains(&origin.epoch.to_string())
                    && message.contains(&other.epoch.to_string()),
                "the message must name both epochs: {message}"
            );
        });
    }
}
