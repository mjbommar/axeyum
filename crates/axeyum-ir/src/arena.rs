//! The term arena: interned storage plus typed, sort-checked builders.

use std::collections::HashMap;

use crate::error::IrError;
use crate::sort::{MAX_BV_WIDTH, Sort, mask};
use crate::term::{ConstructorId, DatatypeId, FuncId, Op, SymbolId, TermId, TermNode};

/// Append-only arena owning symbols and hash-consed terms.
///
/// Structurally equal terms intern to the same [`TermId`]; IDs are assigned
/// densely in insertion order, so identical construction sequences yield
/// identical IDs (determinism rule). Term handles carry no lifetimes; using
/// a `TermId` from a different arena is a contract violation caught only by
/// bounds checks.
#[derive(Debug, Default)]
pub struct TermArena {
    symbols: Vec<(String, Sort)>,
    symbol_lookup: HashMap<String, SymbolId>,
    functions: Vec<FuncDecl>,
    function_lookup: HashMap<String, FuncId>,
    nodes: Vec<TermNode>,
    sorts: Vec<Sort>,
    intern: HashMap<TermNode, TermId>,
    datatypes: Vec<DatatypeInfo>,
    constructors: Vec<ConstructorInfo>,
}

/// Declaration of an uninterpreted function: a name, parameter sorts, and a
/// result sort.
#[derive(Debug, Clone, PartialEq, Eq)]
struct FuncDecl {
    name: String,
    params: Vec<Sort>,
    result: Sort,
}

/// A declared datatype: its name and the constructors that build it (ADR-0022).
#[derive(Debug, Clone, PartialEq, Eq)]
struct DatatypeInfo {
    name: String,
    constructors: Vec<ConstructorId>,
}

/// A datatype constructor: its name, the datatype it builds, and its named,
/// sorted fields (a field sort may be the datatype itself, for recursion).
#[derive(Debug, Clone, PartialEq, Eq)]
struct ConstructorInfo {
    name: String,
    datatype: DatatypeId,
    fields: Vec<(String, Sort)>,
}

impl TermArena {
    /// Creates an empty arena.
    pub fn new() -> Self {
        Self::default()
    }

    /// Number of interned terms.
    pub fn len(&self) -> usize {
        self.nodes.len()
    }

    /// Returns `true` if no terms have been interned.
    pub fn is_empty(&self) -> bool {
        self.nodes.is_empty()
    }

    /// The structural node of `t`.
    ///
    /// # Panics
    ///
    /// Panics if `t` does not belong to this arena.
    pub fn node(&self, t: TermId) -> &TermNode {
        &self.nodes[t.index()]
    }

    /// The sort of `t`.
    ///
    /// # Panics
    ///
    /// Panics if `t` does not belong to this arena.
    pub fn sort_of(&self, t: TermId) -> Sort {
        self.sorts[t.index()]
    }

    /// Looks up a declared symbol by name.
    pub fn find_symbol(&self, name: &str) -> Option<SymbolId> {
        self.symbol_lookup.get(name).copied()
    }

    /// The name and sort of a declared symbol.
    ///
    /// # Panics
    ///
    /// Panics if `s` does not belong to this arena.
    pub fn symbol(&self, s: SymbolId) -> (&str, Sort) {
        let (name, sort) = &self.symbols[s.index()];
        (name, *sort)
    }

    /// Iterates over all declared symbols in declaration order.
    ///
    /// # Panics
    ///
    /// Panics on arena corruption (symbol count exceeding `u32`).
    pub fn symbols(&self) -> impl Iterator<Item = (SymbolId, &str, Sort)> {
        self.symbols.iter().enumerate().map(|(i, (name, sort))| {
            (
                SymbolId(u32::try_from(i).expect("symbol count fits u32")),
                name.as_str(),
                *sort,
            )
        })
    }

    /// Looks up a declared uninterpreted function by name.
    pub fn find_function(&self, name: &str) -> Option<FuncId> {
        self.function_lookup.get(name).copied()
    }

    /// The name, parameter sorts, and result sort of a declared function.
    ///
    /// # Panics
    ///
    /// Panics if `func` does not belong to this arena.
    pub fn function(&self, func: FuncId) -> (&str, &[Sort], Sort) {
        let decl = &self.functions[func.index()];
        (&decl.name, &decl.params, decl.result)
    }

    /// Iterates over all declared functions in declaration order.
    ///
    /// # Panics
    ///
    /// Panics on arena corruption (function count exceeding `u32`).
    pub fn functions(&self) -> impl Iterator<Item = (FuncId, &str, &[Sort], Sort)> {
        self.functions.iter().enumerate().map(|(i, decl)| {
            (
                FuncId(u32::try_from(i).expect("function count fits u32")),
                decl.name.as_str(),
                decl.params.as_slice(),
                decl.result,
            )
        })
    }

    fn intern_node(&mut self, node: TermNode, sort: Sort) -> TermId {
        if let Some(&id) = self.intern.get(&node) {
            return id;
        }
        let id = TermId(u32::try_from(self.nodes.len()).expect("term count fits u32"));
        self.nodes.push(node.clone());
        self.sorts.push(sort);
        self.intern.insert(node, id);
        id
    }

    // ----- declarations -------------------------------------------------

    /// Declares a symbol, or returns the existing one if `name` was already
    /// declared with the same sort.
    ///
    /// # Errors
    ///
    /// Returns [`IrError::SymbolSortConflict`] if `name` exists with a
    /// different sort, or [`IrError::InvalidWidth`] for a bad BV sort.
    ///
    /// # Panics
    ///
    /// Panics on arena corruption (symbol count exceeding `u32`).
    pub fn declare(&mut self, name: &str, sort: Sort) -> Result<SymbolId, IrError> {
        if let Sort::BitVec(w) = sort {
            check_width(w)?;
        }
        if let Some(&existing) = self.symbol_lookup.get(name) {
            let (_, existing_sort) = self.symbols[existing.index()];
            if existing_sort == sort {
                return Ok(existing);
            }
            return Err(IrError::SymbolSortConflict {
                name: name.to_owned(),
                existing: existing_sort,
                requested: sort,
            });
        }
        let id = SymbolId(u32::try_from(self.symbols.len()).expect("symbol count fits u32"));
        self.symbols.push((name.to_owned(), sort));
        self.symbol_lookup.insert(name.to_owned(), id);
        Ok(id)
    }

    /// The variable term referring to a declared symbol.
    ///
    /// # Panics
    ///
    /// Panics if `s` does not belong to this arena.
    pub fn var(&mut self, s: SymbolId) -> TermId {
        let sort = self.symbols[s.index()].1;
        self.intern_node(TermNode::Symbol(s), sort)
    }

    /// Declares a bit-vector symbol and returns its variable term.
    ///
    /// # Errors
    ///
    /// See [`TermArena::declare`].
    pub fn bv_var(&mut self, name: &str, width: u32) -> Result<TermId, IrError> {
        let s = self.declare(name, Sort::BitVec(width))?;
        Ok(self.var(s))
    }

    /// Declares a Boolean symbol and returns its variable term.
    ///
    /// # Errors
    ///
    /// See [`TermArena::declare`].
    pub fn bool_var(&mut self, name: &str) -> Result<TermId, IrError> {
        let s = self.declare(name, Sort::Bool)?;
        Ok(self.var(s))
    }

    // ----- constants ----------------------------------------------------

    /// A Boolean constant.
    pub fn bool_const(&mut self, b: bool) -> TermId {
        self.intern_node(TermNode::BoolConst(b), Sort::Bool)
    }

    /// A bit-vector constant.
    ///
    /// # Errors
    ///
    /// Returns [`IrError::InvalidWidth`] for widths outside
    /// `1..=MAX_BV_WIDTH`, or [`IrError::ValueOutOfRange`] if `value` does
    /// not fit in `width` bits.
    pub fn bv_const(&mut self, width: u32, value: u128) -> Result<TermId, IrError> {
        check_width(width)?;
        if value & !mask(width) != 0 {
            return Err(IrError::ValueOutOfRange { width, value });
        }
        Ok(self.intern_node(TermNode::BvConst { width, value }, Sort::BitVec(width)))
    }

    // ----- sort-check helpers -------------------------------------------

    fn expect_bool(&self, t: TermId) -> Result<(), IrError> {
        match self.sort_of(t) {
            Sort::Bool => Ok(()),
            found @ (Sort::BitVec(_)
            | Sort::Array { .. }
            | Sort::Int
            | Sort::Real
            | Sort::Datatype(_)) => Err(IrError::SortMismatch {
                expected: "Bool",
                found,
            }),
        }
    }

    fn expect_bv(&self, t: TermId) -> Result<u32, IrError> {
        match self.sort_of(t) {
            Sort::BitVec(w) => Ok(w),
            found @ (Sort::Bool
            | Sort::Array { .. }
            | Sort::Int
            | Sort::Real
            | Sort::Datatype(_)) => Err(IrError::SortMismatch {
                expected: "BitVec",
                found,
            }),
        }
    }

    fn expect_same_bv(&self, a: TermId, b: TermId) -> Result<u32, IrError> {
        let wa = self.expect_bv(a)?;
        let wb = self.expect_bv(b)?;
        if wa == wb {
            Ok(wa)
        } else {
            Err(IrError::SortsDiffer(Sort::BitVec(wa), Sort::BitVec(wb)))
        }
    }

    fn app(&mut self, op: Op, args: &[TermId], sort: Sort) -> TermId {
        self.intern_node(
            TermNode::App {
                op,
                args: args.into(),
            },
            sort,
        )
    }

    // ----- datatypes (ADR-0022) -----------------------------------------

    /// Declares a datatype with no constructors yet, returning its id. Add
    /// constructors with [`Self::add_constructor`]; a constructor field may use
    /// `Sort::Datatype(id)` of this same id, so recursive datatypes are built by
    /// declaring first, then adding constructors.
    ///
    /// # Panics
    ///
    /// Panics on arena corruption (datatype count exceeding `u32`).
    pub fn declare_datatype(&mut self, name: &str) -> DatatypeId {
        let id = DatatypeId(u32::try_from(self.datatypes.len()).expect("datatype count fits u32"));
        self.datatypes.push(DatatypeInfo {
            name: name.to_owned(),
            constructors: Vec::new(),
        });
        id
    }

    /// Adds a constructor (name + named, sorted fields) to a declared datatype,
    /// returning its id.
    ///
    /// # Panics
    ///
    /// Panics if `datatype` does not belong to this arena.
    pub fn add_constructor(
        &mut self,
        datatype: DatatypeId,
        name: &str,
        fields: &[(String, Sort)],
    ) -> ConstructorId {
        let id = ConstructorId(
            u32::try_from(self.constructors.len()).expect("constructor count fits u32"),
        );
        self.constructors.push(ConstructorInfo {
            name: name.to_owned(),
            datatype,
            fields: fields.to_vec(),
        });
        self.datatypes[datatype.index()].constructors.push(id);
        id
    }

    /// The datatype's name.
    ///
    /// # Panics
    ///
    /// Panics if `id` does not belong to this arena.
    pub fn datatype_name(&self, id: DatatypeId) -> &str {
        &self.datatypes[id.index()].name
    }

    /// The constructor ids of a datatype, in declaration order.
    ///
    /// # Panics
    ///
    /// Panics if `id` does not belong to this arena.
    pub fn datatype_constructors(&self, id: DatatypeId) -> &[ConstructorId] {
        &self.datatypes[id.index()].constructors
    }

    /// The datatype a constructor builds.
    ///
    /// # Panics
    ///
    /// Panics if `ctor` does not belong to this arena.
    pub fn constructor_datatype(&self, ctor: ConstructorId) -> DatatypeId {
        self.constructors[ctor.index()].datatype
    }

    /// A constructor's name.
    pub fn constructor_name(&self, ctor: ConstructorId) -> &str {
        &self.constructors[ctor.index()].name
    }

    /// A constructor's `(field name, sort)` list.
    pub fn constructor_fields(&self, ctor: ConstructorId) -> &[(String, Sort)] {
        &self.constructors[ctor.index()].fields
    }

    /// Builds `constructor(args...)`, a value of the constructor's datatype.
    ///
    /// # Errors
    ///
    /// [`IrError::ArityMismatch`] if the wrong number of fields is supplied, or
    /// [`IrError::SortMismatch`] if a field argument has the wrong sort.
    pub fn construct(&mut self, ctor: ConstructorId, args: &[TermId]) -> Result<TermId, IrError> {
        let info = &self.constructors[ctor.index()];
        if args.len() != info.fields.len() {
            return Err(IrError::ArityMismatch {
                expected: info.fields.len(),
                found: args.len(),
            });
        }
        let datatype = info.datatype;
        let field_sorts: Vec<Sort> = info.fields.iter().map(|(_, sort)| *sort).collect();
        for (&arg, expected) in args.iter().zip(&field_sorts) {
            let found = self.sort_of(arg);
            if found != *expected {
                return Err(IrError::SortsDiffer(*expected, found));
            }
        }
        Ok(self.app(
            Op::DtConstruct {
                constructor: ctor,
                datatype,
            },
            args,
            Sort::Datatype(datatype),
        ))
    }

    /// Builds the selector for field `index` of `constructor` applied to `value`.
    ///
    /// # Errors
    ///
    /// [`IrError::SortMismatch`] if `value` is not of the constructor's datatype,
    /// or [`IrError::ArityMismatch`] if `index` is out of range.
    pub fn dt_select(
        &mut self,
        ctor: ConstructorId,
        index: u32,
        value: TermId,
    ) -> Result<TermId, IrError> {
        let info = &self.constructors[ctor.index()];
        let datatype = info.datatype;
        let field_count = info.fields.len();
        let result_sort = info
            .fields
            .get(index as usize)
            .map(|(_, sort)| *sort)
            .ok_or(IrError::ArityMismatch {
                expected: field_count,
                found: index as usize + 1,
            })?;
        let found = self.sort_of(value);
        if found != Sort::Datatype(datatype) {
            return Err(IrError::SortMismatch {
                expected: "datatype value",
                found,
            });
        }
        Ok(self.app(
            Op::DtSelect {
                constructor: ctor,
                index,
            },
            &[value],
            result_sort,
        ))
    }

    /// Builds the tester `is-constructor(value)` (result `Bool`).
    ///
    /// # Errors
    ///
    /// [`IrError::SortMismatch`] if `value` is not of the constructor's datatype.
    pub fn dt_test(&mut self, ctor: ConstructorId, value: TermId) -> Result<TermId, IrError> {
        let datatype = self.constructors[ctor.index()].datatype;
        let found = self.sort_of(value);
        if found != Sort::Datatype(datatype) {
            return Err(IrError::SortMismatch {
                expected: "datatype value",
                found,
            });
        }
        Ok(self.app(Op::DtTest(ctor), &[value], Sort::Bool))
    }

    // ----- Boolean operators --------------------------------------------

    /// Boolean negation.
    ///
    /// # Errors
    ///
    /// Returns [`IrError::SortMismatch`] unless `a` is `Bool`.
    pub fn not(&mut self, a: TermId) -> Result<TermId, IrError> {
        self.expect_bool(a)?;
        Ok(self.app(Op::BoolNot, &[a], Sort::Bool))
    }

    /// Boolean conjunction.
    ///
    /// # Errors
    ///
    /// Returns [`IrError::SortMismatch`] unless both operands are `Bool`.
    pub fn and(&mut self, a: TermId, b: TermId) -> Result<TermId, IrError> {
        self.expect_bool(a)?;
        self.expect_bool(b)?;
        Ok(self.app(Op::BoolAnd, &[a, b], Sort::Bool))
    }

    /// Boolean disjunction.
    ///
    /// # Errors
    ///
    /// Returns [`IrError::SortMismatch`] unless both operands are `Bool`.
    pub fn or(&mut self, a: TermId, b: TermId) -> Result<TermId, IrError> {
        self.expect_bool(a)?;
        self.expect_bool(b)?;
        Ok(self.app(Op::BoolOr, &[a, b], Sort::Bool))
    }

    /// Boolean exclusive or.
    ///
    /// # Errors
    ///
    /// Returns [`IrError::SortMismatch`] unless both operands are `Bool`.
    pub fn xor(&mut self, a: TermId, b: TermId) -> Result<TermId, IrError> {
        self.expect_bool(a)?;
        self.expect_bool(b)?;
        Ok(self.app(Op::BoolXor, &[a, b], Sort::Bool))
    }

    // ----- bit-vector operators -----------------------------------------

    /// Bitwise negation.
    ///
    /// # Errors
    ///
    /// Returns [`IrError::SortMismatch`] unless `a` is a bit-vector.
    pub fn bv_not(&mut self, a: TermId) -> Result<TermId, IrError> {
        let w = self.expect_bv(a)?;
        Ok(self.app(Op::BvNot, &[a], Sort::BitVec(w)))
    }

    /// Bitwise and.
    ///
    /// # Errors
    ///
    /// Returns [`IrError::SortMismatch`] / [`IrError::SortsDiffer`] unless
    /// both operands are bit-vectors of the same width.
    pub fn bv_and(&mut self, a: TermId, b: TermId) -> Result<TermId, IrError> {
        let w = self.expect_same_bv(a, b)?;
        Ok(self.app(Op::BvAnd, &[a, b], Sort::BitVec(w)))
    }

    /// Bitwise or.
    ///
    /// # Errors
    ///
    /// Same conditions as [`TermArena::bv_and`].
    pub fn bv_or(&mut self, a: TermId, b: TermId) -> Result<TermId, IrError> {
        let w = self.expect_same_bv(a, b)?;
        Ok(self.app(Op::BvOr, &[a, b], Sort::BitVec(w)))
    }

    /// Bitwise xor.
    ///
    /// # Errors
    ///
    /// Same conditions as [`TermArena::bv_and`].
    pub fn bv_xor(&mut self, a: TermId, b: TermId) -> Result<TermId, IrError> {
        let w = self.expect_same_bv(a, b)?;
        Ok(self.app(Op::BvXor, &[a, b], Sort::BitVec(w)))
    }

    /// Wrapping addition modulo `2^width`.
    ///
    /// # Errors
    ///
    /// Same conditions as [`TermArena::bv_and`].
    pub fn bv_add(&mut self, a: TermId, b: TermId) -> Result<TermId, IrError> {
        let w = self.expect_same_bv(a, b)?;
        Ok(self.app(Op::BvAdd, &[a, b], Sort::BitVec(w)))
    }

    /// Unsigned less-than; the result is `Bool`.
    ///
    /// # Errors
    ///
    /// Same conditions as [`TermArena::bv_and`].
    pub fn bv_ult(&mut self, a: TermId, b: TermId) -> Result<TermId, IrError> {
        self.expect_same_bv(a, b)?;
        Ok(self.app(Op::BvUlt, &[a, b], Sort::Bool))
    }

    /// Equality over any shared sort; the result is `Bool`.
    ///
    /// # Errors
    ///
    /// Returns [`IrError::SortsDiffer`] if the operand sorts differ.
    pub fn eq(&mut self, a: TermId, b: TermId) -> Result<TermId, IrError> {
        let sa = self.sort_of(a);
        let sb = self.sort_of(b);
        if sa != sb {
            return Err(IrError::SortsDiffer(sa, sb));
        }
        Ok(self.app(Op::Eq, &[a, b], Sort::Bool))
    }

    /// If-then-else with a `Bool` condition and same-sort branches.
    ///
    /// # Errors
    ///
    /// Returns [`IrError::SortMismatch`] unless `c` is `Bool`, or
    /// [`IrError::SortsDiffer`] if the branch sorts differ.
    pub fn ite(&mut self, c: TermId, t: TermId, e: TermId) -> Result<TermId, IrError> {
        self.expect_bool(c)?;
        let st = self.sort_of(t);
        let se = self.sort_of(e);
        if st != se {
            return Err(IrError::SortsDiffer(st, se));
        }
        Ok(self.app(Op::Ite, &[c, t, e], st))
    }

    /// Bit slice `[hi:lo]` (inclusive); result width is `hi - lo + 1`.
    ///
    /// # Errors
    ///
    /// Returns [`IrError::SortMismatch`] unless `a` is a bit-vector, or
    /// [`IrError::ExtractOutOfRange`] unless `lo <= hi < width`.
    pub fn extract(&mut self, hi: u32, lo: u32, a: TermId) -> Result<TermId, IrError> {
        let w = self.expect_bv(a)?;
        if hi < lo || hi >= w {
            return Err(IrError::ExtractOutOfRange { hi, lo, width: w });
        }
        let out = hi - lo + 1;
        Ok(self.app(Op::Extract { hi, lo }, &[a], Sort::BitVec(out)))
    }

    /// Concatenation; `a` becomes the high bits.
    ///
    /// # Errors
    ///
    /// Returns [`IrError::SortMismatch`] unless both operands are
    /// bit-vectors, or [`IrError::ConcatTooWide`] if the result exceeds
    /// [`MAX_BV_WIDTH`] (ADR-0003).
    pub fn concat(&mut self, a: TermId, b: TermId) -> Result<TermId, IrError> {
        let wa = self.expect_bv(a)?;
        let wb = self.expect_bv(b)?;
        let out = checked_output_width(wa, wb)?;
        Ok(self.app(Op::Concat, &[a, b], Sort::BitVec(out)))
    }
}

impl TermArena {
    fn bv_bin(&mut self, op: Op, a: TermId, b: TermId) -> Result<TermId, IrError> {
        let w = self.expect_same_bv(a, b)?;
        Ok(self.app(op, &[a, b], Sort::BitVec(w)))
    }

    fn bv_cmp(&mut self, op: Op, a: TermId, b: TermId) -> Result<TermId, IrError> {
        self.expect_same_bv(a, b)?;
        Ok(self.app(op, &[a, b], Sort::Bool))
    }

    /// Boolean implication.
    ///
    /// # Errors
    ///
    /// Returns [`IrError::SortMismatch`] unless both operands are `Bool`.
    pub fn implies(&mut self, a: TermId, b: TermId) -> Result<TermId, IrError> {
        self.expect_bool(a)?;
        self.expect_bool(b)?;
        Ok(self.app(Op::BoolImplies, &[a, b], Sort::Bool))
    }

    /// Bitwise nand.
    ///
    /// # Errors
    ///
    /// Same conditions as [`TermArena::bv_and`].
    pub fn bv_nand(&mut self, a: TermId, b: TermId) -> Result<TermId, IrError> {
        self.bv_bin(Op::BvNand, a, b)
    }

    /// Bitwise nor.
    ///
    /// # Errors
    ///
    /// Same conditions as [`TermArena::bv_and`].
    pub fn bv_nor(&mut self, a: TermId, b: TermId) -> Result<TermId, IrError> {
        self.bv_bin(Op::BvNor, a, b)
    }

    /// Bitwise xnor.
    ///
    /// # Errors
    ///
    /// Same conditions as [`TermArena::bv_and`].
    pub fn bv_xnor(&mut self, a: TermId, b: TermId) -> Result<TermId, IrError> {
        self.bv_bin(Op::BvXnor, a, b)
    }

    /// Two's-complement negation, wrapping.
    ///
    /// # Errors
    ///
    /// Returns [`IrError::SortMismatch`] unless `a` is a bit-vector.
    pub fn bv_neg(&mut self, a: TermId) -> Result<TermId, IrError> {
        let w = self.expect_bv(a)?;
        Ok(self.app(Op::BvNeg, &[a], Sort::BitVec(w)))
    }

    /// Subtraction modulo `2^width`.
    ///
    /// # Errors
    ///
    /// Same conditions as [`TermArena::bv_and`].
    pub fn bv_sub(&mut self, a: TermId, b: TermId) -> Result<TermId, IrError> {
        self.bv_bin(Op::BvSub, a, b)
    }

    /// Multiplication modulo `2^width`.
    ///
    /// # Errors
    ///
    /// Same conditions as [`TermArena::bv_and`].
    pub fn bv_mul(&mut self, a: TermId, b: TermId) -> Result<TermId, IrError> {
        self.bv_bin(Op::BvMul, a, b)
    }

    /// Unsigned division (total: division by zero yields all-ones).
    ///
    /// # Errors
    ///
    /// Same conditions as [`TermArena::bv_and`].
    pub fn bv_udiv(&mut self, a: TermId, b: TermId) -> Result<TermId, IrError> {
        self.bv_bin(Op::BvUdiv, a, b)
    }

    /// Unsigned remainder (total: remainder by zero yields the dividend).
    ///
    /// # Errors
    ///
    /// Same conditions as [`TermArena::bv_and`].
    pub fn bv_urem(&mut self, a: TermId, b: TermId) -> Result<TermId, IrError> {
        self.bv_bin(Op::BvUrem, a, b)
    }

    /// Signed division (truncating; total per the SMT-LIB expansion).
    ///
    /// # Errors
    ///
    /// Same conditions as [`TermArena::bv_and`].
    pub fn bv_sdiv(&mut self, a: TermId, b: TermId) -> Result<TermId, IrError> {
        self.bv_bin(Op::BvSdiv, a, b)
    }

    /// Signed remainder, sign follows the dividend (total).
    ///
    /// # Errors
    ///
    /// Same conditions as [`TermArena::bv_and`].
    pub fn bv_srem(&mut self, a: TermId, b: TermId) -> Result<TermId, IrError> {
        self.bv_bin(Op::BvSrem, a, b)
    }

    /// Signed modulo, sign follows the divisor (total).
    ///
    /// # Errors
    ///
    /// Same conditions as [`TermArena::bv_and`].
    pub fn bv_smod(&mut self, a: TermId, b: TermId) -> Result<TermId, IrError> {
        self.bv_bin(Op::BvSmod, a, b)
    }

    /// Logical shift left by the numeric value of `b`.
    ///
    /// # Errors
    ///
    /// Same conditions as [`TermArena::bv_and`].
    pub fn bv_shl(&mut self, a: TermId, b: TermId) -> Result<TermId, IrError> {
        self.bv_bin(Op::BvShl, a, b)
    }

    /// Logical shift right by the numeric value of `b`.
    ///
    /// # Errors
    ///
    /// Same conditions as [`TermArena::bv_and`].
    pub fn bv_lshr(&mut self, a: TermId, b: TermId) -> Result<TermId, IrError> {
        self.bv_bin(Op::BvLshr, a, b)
    }

    /// Arithmetic shift right by the numeric value of `b`.
    ///
    /// # Errors
    ///
    /// Same conditions as [`TermArena::bv_and`].
    pub fn bv_ashr(&mut self, a: TermId, b: TermId) -> Result<TermId, IrError> {
        self.bv_bin(Op::BvAshr, a, b)
    }

    /// Unsigned less-or-equal.
    ///
    /// # Errors
    ///
    /// Same conditions as [`TermArena::bv_and`].
    pub fn bv_ule(&mut self, a: TermId, b: TermId) -> Result<TermId, IrError> {
        self.bv_cmp(Op::BvUle, a, b)
    }

    /// Unsigned greater-than.
    ///
    /// # Errors
    ///
    /// Same conditions as [`TermArena::bv_and`].
    pub fn bv_ugt(&mut self, a: TermId, b: TermId) -> Result<TermId, IrError> {
        self.bv_cmp(Op::BvUgt, a, b)
    }

    /// Unsigned greater-or-equal.
    ///
    /// # Errors
    ///
    /// Same conditions as [`TermArena::bv_and`].
    pub fn bv_uge(&mut self, a: TermId, b: TermId) -> Result<TermId, IrError> {
        self.bv_cmp(Op::BvUge, a, b)
    }

    /// Signed less-than.
    ///
    /// # Errors
    ///
    /// Same conditions as [`TermArena::bv_and`].
    pub fn bv_slt(&mut self, a: TermId, b: TermId) -> Result<TermId, IrError> {
        self.bv_cmp(Op::BvSlt, a, b)
    }

    /// Signed less-or-equal.
    ///
    /// # Errors
    ///
    /// Same conditions as [`TermArena::bv_and`].
    pub fn bv_sle(&mut self, a: TermId, b: TermId) -> Result<TermId, IrError> {
        self.bv_cmp(Op::BvSle, a, b)
    }

    /// Signed greater-than.
    ///
    /// # Errors
    ///
    /// Same conditions as [`TermArena::bv_and`].
    pub fn bv_sgt(&mut self, a: TermId, b: TermId) -> Result<TermId, IrError> {
        self.bv_cmp(Op::BvSgt, a, b)
    }

    /// Signed greater-or-equal.
    ///
    /// # Errors
    ///
    /// Same conditions as [`TermArena::bv_and`].
    pub fn bv_sge(&mut self, a: TermId, b: TermId) -> Result<TermId, IrError> {
        self.bv_cmp(Op::BvSge, a, b)
    }

    /// Equality as a bit: `BV(1)` one if equal, zero otherwise.
    ///
    /// # Errors
    ///
    /// Same conditions as [`TermArena::bv_and`].
    pub fn bv_comp(&mut self, a: TermId, b: TermId) -> Result<TermId, IrError> {
        self.expect_same_bv(a, b)?;
        Ok(self.app(Op::BvComp, &[a, b], Sort::BitVec(1)))
    }

    /// `bvuaddo` — unsigned addition overflow: the `(w+1)`-bit sum carries out.
    ///
    /// # Errors
    ///
    /// Returns [`IrError`] from the builders (e.g. operands of differing width).
    pub fn bv_uaddo(&mut self, a: TermId, b: TermId) -> Result<TermId, IrError> {
        let w = self.expect_same_bv(a, b)?;
        let ae = self.zero_ext(1, a)?;
        let be = self.zero_ext(1, b)?;
        let s = self.bv_add(ae, be)?;
        let carry = self.extract(w, w, s)?;
        let one1 = self.bv_const(1, 1)?;
        self.eq(carry, one1)
    }

    /// `bvsaddo` — signed addition overflow: operands share a sign but the sum's
    /// sign differs.
    ///
    /// # Errors
    ///
    /// Returns [`IrError`] from the builders.
    pub fn bv_saddo(&mut self, a: TermId, b: TermId) -> Result<TermId, IrError> {
        let w = self.expect_same_bv(a, b)?;
        let sa = self.extract(w - 1, w - 1, a)?;
        let sb = self.extract(w - 1, w - 1, b)?;
        let s = self.bv_add(a, b)?;
        let ss = self.extract(w - 1, w - 1, s)?;
        let same = self.eq(sa, sb)?;
        let ss_eq_sa = self.eq(ss, sa)?;
        let differs = self.not(ss_eq_sa)?;
        self.and(same, differs)
    }

    /// `bvusubo` — unsigned subtraction overflow (borrow): `a < b` unsigned.
    ///
    /// # Errors
    ///
    /// Returns [`IrError`] from the builders.
    pub fn bv_usubo(&mut self, a: TermId, b: TermId) -> Result<TermId, IrError> {
        self.expect_same_bv(a, b)?;
        self.bv_ult(a, b)
    }

    /// `bvssubo` — signed subtraction overflow: operands differ in sign and the
    /// difference's sign differs from `a`.
    ///
    /// # Errors
    ///
    /// Returns [`IrError`] from the builders.
    pub fn bv_ssubo(&mut self, a: TermId, b: TermId) -> Result<TermId, IrError> {
        let w = self.expect_same_bv(a, b)?;
        let sa = self.extract(w - 1, w - 1, a)?;
        let sb = self.extract(w - 1, w - 1, b)?;
        let s = self.bv_sub(a, b)?;
        let ss = self.extract(w - 1, w - 1, s)?;
        let sa_eq_sb = self.eq(sa, sb)?;
        let signs_differ = self.not(sa_eq_sb)?;
        let ss_eq_sa = self.eq(ss, sa)?;
        let res_differs = self.not(ss_eq_sa)?;
        self.and(signs_differ, res_differs)
    }

    /// `bvnego` — negation overflow: `a` is the signed minimum (`−2^(w−1)`).
    ///
    /// # Errors
    ///
    /// Returns [`IrError`] from the builders.
    pub fn bv_nego(&mut self, a: TermId) -> Result<TermId, IrError> {
        let w = self.expect_bv(a)?;
        let min = self.bv_const(w, 1u128 << (w - 1))?;
        self.eq(a, min)
    }

    /// `bvumulo` — unsigned multiplication overflow: the high `w` bits of the
    /// `2w`-bit product are nonzero.
    ///
    /// # Errors
    ///
    /// Returns [`IrError`] from the builders (incl. [`IrError::ConcatTooWide`] if
    /// `2w` exceeds [`MAX_BV_WIDTH`]).
    pub fn bv_umulo(&mut self, a: TermId, b: TermId) -> Result<TermId, IrError> {
        let w = self.expect_same_bv(a, b)?;
        let ae = self.zero_ext(w, a)?;
        let be = self.zero_ext(w, b)?;
        let p = self.bv_mul(ae, be)?;
        let hi = self.extract(2 * w - 1, w, p)?;
        let zero = self.bv_const(w, 0)?;
        let hi_zero = self.eq(hi, zero)?;
        self.not(hi_zero)
    }

    /// `bvsmulo` — signed multiplication overflow: the `2w`-bit signed product
    /// does not fit in `w` bits (its low `w` bits, sign-extended, differ from it).
    ///
    /// # Errors
    ///
    /// Returns [`IrError`] from the builders (incl. [`IrError::ConcatTooWide`] if
    /// `2w` exceeds [`MAX_BV_WIDTH`]).
    pub fn bv_smulo(&mut self, a: TermId, b: TermId) -> Result<TermId, IrError> {
        let w = self.expect_same_bv(a, b)?;
        let ae = self.sign_ext(w, a)?;
        let be = self.sign_ext(w, b)?;
        let p = self.bv_mul(ae, be)?;
        let lo = self.extract(w - 1, 0, p)?;
        let lo_ext = self.sign_ext(w, lo)?;
        let fits = self.eq(p, lo_ext)?;
        self.not(fits)
    }

    /// Zero extension by `by` bits.
    ///
    /// # Errors
    ///
    /// Returns [`IrError::SortMismatch`] unless `a` is a bit-vector, or
    /// [`IrError::ConcatTooWide`] if the result exceeds [`MAX_BV_WIDTH`].
    pub fn zero_ext(&mut self, by: u32, a: TermId) -> Result<TermId, IrError> {
        let w = self.expect_bv(a)?;
        let out = checked_output_width(w, by)?;
        Ok(self.app(Op::ZeroExt { by }, &[a], Sort::BitVec(out)))
    }

    /// Sign extension by `by` bits.
    ///
    /// # Errors
    ///
    /// Same conditions as [`TermArena::zero_ext`].
    pub fn sign_ext(&mut self, by: u32, a: TermId) -> Result<TermId, IrError> {
        let w = self.expect_bv(a)?;
        let out = checked_output_width(w, by)?;
        Ok(self.app(Op::SignExt { by }, &[a], Sort::BitVec(out)))
    }

    /// Rotate left by a constant; the amount is normalized modulo width at
    /// build time so equivalent rotations intern to the same term.
    ///
    /// # Errors
    ///
    /// Returns [`IrError::SortMismatch`] unless `a` is a bit-vector.
    pub fn rotate_left(&mut self, by: u32, a: TermId) -> Result<TermId, IrError> {
        let w = self.expect_bv(a)?;
        Ok(self.app(Op::RotateLeft { by: by % w }, &[a], Sort::BitVec(w)))
    }

    /// Rotate right by a constant; the amount is normalized modulo width at
    /// build time so equivalent rotations intern to the same term.
    ///
    /// # Errors
    ///
    /// Returns [`IrError::SortMismatch`] unless `a` is a bit-vector.
    pub fn rotate_right(&mut self, by: u32, a: TermId) -> Result<TermId, IrError> {
        let w = self.expect_bv(a)?;
        Ok(self.app(Op::RotateRight { by: by % w }, &[a], Sort::BitVec(w)))
    }

    // ----- arrays (ADR-0010) --------------------------------------------

    /// Declares an array symbol `Array(index -> element)` and returns its
    /// variable term.
    ///
    /// # Errors
    ///
    /// Returns [`IrError::InvalidWidth`] for an index or element width outside
    /// `1..=MAX_BV_WIDTH`, or [`IrError::SymbolSortConflict`] on a name reuse
    /// with a different sort.
    pub fn array_var(&mut self, name: &str, index: u32, element: u32) -> Result<TermId, IrError> {
        check_width(index)?;
        check_width(element)?;
        let symbol = self.declare(name, Sort::Array { index, element })?;
        Ok(self.var(symbol))
    }

    /// Array read `select(array, idx)`; the result has the element sort.
    ///
    /// # Errors
    ///
    /// Returns [`IrError::SortMismatch`] unless `array` is an array and `idx`
    /// is a bit-vector, or [`IrError::SortsDiffer`] if `idx`'s width does not
    /// match the array index width.
    pub fn select(&mut self, array: TermId, idx: TermId) -> Result<TermId, IrError> {
        let (index_width, element_width) = self.expect_array(array)?;
        let idx_width = self.expect_bv(idx)?;
        if idx_width != index_width {
            return Err(IrError::SortsDiffer(
                Sort::BitVec(idx_width),
                Sort::BitVec(index_width),
            ));
        }
        Ok(self.app(Op::Select, &[array, idx], Sort::BitVec(element_width)))
    }

    /// Array write `store(array, idx, element)`; the result has the array sort.
    ///
    /// # Errors
    ///
    /// Returns [`IrError::SortMismatch`] unless `array` is an array and `idx`,
    /// `element` are bit-vectors, or [`IrError::SortsDiffer`] if the widths do
    /// not match the array sort.
    pub fn store(
        &mut self,
        array: TermId,
        idx: TermId,
        element: TermId,
    ) -> Result<TermId, IrError> {
        let (index_width, element_width) = self.expect_array(array)?;
        let idx_width = self.expect_bv(idx)?;
        if idx_width != index_width {
            return Err(IrError::SortsDiffer(
                Sort::BitVec(idx_width),
                Sort::BitVec(index_width),
            ));
        }
        let elem_width = self.expect_bv(element)?;
        if elem_width != element_width {
            return Err(IrError::SortsDiffer(
                Sort::BitVec(elem_width),
                Sort::BitVec(element_width),
            ));
        }
        Ok(self.app(
            Op::Store,
            &[array, idx, element],
            Sort::Array {
                index: index_width,
                element: element_width,
            },
        ))
    }

    /// Constant array `((as const (Array (_ BitVec index) (_ BitVec e))) value)`:
    /// every index maps to `value`. The element width is taken from `value`.
    ///
    /// # Errors
    ///
    /// Returns [`IrError::InvalidWidth`] for a bad index width, or
    /// [`IrError::SortMismatch`] unless `value` is a bit-vector.
    pub fn const_array(&mut self, index: u32, value: TermId) -> Result<TermId, IrError> {
        check_width(index)?;
        let element = self.expect_bv(value)?;
        Ok(self.app(Op::ConstArray { index }, &[value], Sort::Array { index, element }))
    }

    /// `bv2nat`: the unsigned integer value of a bit-vector (result sort `Int`).
    ///
    /// # Errors
    ///
    /// Returns [`IrError::SortMismatch`] unless `x` is a bit-vector.
    pub fn bv2nat(&mut self, x: TermId) -> Result<TermId, IrError> {
        self.expect_bv(x)?;
        Ok(self.app(Op::Bv2Nat, &[x], Sort::Int))
    }

    /// `(_ int2bv width)`: the bit-vector of `width` bits equal to the operand
    /// integer reduced mod `2^width`.
    ///
    /// # Errors
    ///
    /// Returns [`IrError::InvalidWidth`] for a bad width, or
    /// [`IrError::SortMismatch`] unless `x` is an integer.
    pub fn int2bv(&mut self, width: u32, x: TermId) -> Result<TermId, IrError> {
        check_width(width)?;
        self.expect_int(x)?;
        Ok(self.app(Op::Int2Bv { width }, &[x], Sort::BitVec(width)))
    }

    fn expect_array(&self, t: TermId) -> Result<(u32, u32), IrError> {
        match self.sort_of(t) {
            Sort::Array { index, element } => Ok((index, element)),
            found @ (Sort::Bool | Sort::BitVec(_) | Sort::Int | Sort::Real | Sort::Datatype(_)) => {
                Err(IrError::SortMismatch {
                    expected: "Array",
                    found,
                })
            }
        }
    }

    // ----- uninterpreted functions (ADR-0013) ---------------------------

    /// Declares an uninterpreted function with the given scalar parameter sorts
    /// and result sort, or returns the existing one if `name` was already
    /// declared with the identical signature.
    ///
    /// # Errors
    ///
    /// Returns [`IrError::SortMismatch`] if any parameter or the result is an
    /// array sort (functions are scalar in the supported fragment),
    /// [`IrError::InvalidWidth`] for a bad bit-vector width, or
    /// [`IrError::FunctionSignatureConflict`] if `name` exists with a different
    /// signature.
    ///
    /// # Panics
    ///
    /// Panics on arena corruption (function count exceeding `u32`).
    pub fn declare_fun(
        &mut self,
        name: &str,
        params: &[Sort],
        result: Sort,
    ) -> Result<FuncId, IrError> {
        for &sort in params {
            check_scalar_width(sort)?;
        }
        check_scalar_width(result)?;
        if let Some(&existing) = self.function_lookup.get(name) {
            let decl = &self.functions[existing.index()];
            if decl.params == params && decl.result == result {
                return Ok(existing);
            }
            return Err(IrError::FunctionSignatureConflict {
                name: name.to_owned(),
            });
        }
        let id = FuncId(u32::try_from(self.functions.len()).expect("function count fits u32"));
        self.functions.push(FuncDecl {
            name: name.to_owned(),
            params: params.to_vec(),
            result,
        });
        self.function_lookup.insert(name.to_owned(), id);
        Ok(id)
    }

    /// Application `func(args)` of a declared uninterpreted function; the result
    /// has the function's declared result sort.
    ///
    /// # Errors
    ///
    /// Returns [`IrError::ArityMismatch`] if `args` has the wrong length, or
    /// [`IrError::SortsDiffer`] if an argument's sort does not match the
    /// corresponding parameter sort.
    ///
    /// # Panics
    ///
    /// Panics if `func` does not belong to this arena.
    pub fn apply(&mut self, func: FuncId, args: &[TermId]) -> Result<TermId, IrError> {
        let (params, result) = {
            let decl = &self.functions[func.index()];
            (decl.params.clone(), decl.result)
        };
        if args.len() != params.len() {
            return Err(IrError::ArityMismatch {
                expected: params.len(),
                found: args.len(),
            });
        }
        for (&arg, &param) in args.iter().zip(&params) {
            let actual = self.sort_of(arg);
            if actual != param {
                return Err(IrError::SortsDiffer(actual, param));
            }
        }
        Ok(self.app(Op::Apply(func), args, result))
    }

    // ----- linear integer arithmetic (ADR-0014) -------------------------

    /// An integer constant.
    pub fn int_const(&mut self, value: i128) -> TermId {
        self.intern_node(TermNode::IntConst(value), Sort::Int)
    }

    /// Declares an integer symbol and returns its variable term.
    ///
    /// # Errors
    ///
    /// Returns [`IrError::SymbolSortConflict`] on a name reuse with a different
    /// sort.
    pub fn int_var(&mut self, name: &str) -> Result<TermId, IrError> {
        let s = self.declare(name, Sort::Int)?;
        Ok(self.var(s))
    }

    fn expect_int(&self, t: TermId) -> Result<(), IrError> {
        match self.sort_of(t) {
            Sort::Int => Ok(()),
            found @ (Sort::Bool
            | Sort::BitVec(_)
            | Sort::Array { .. }
            | Sort::Real
            | Sort::Datatype(_)) => Err(IrError::SortMismatch {
                expected: "Int",
                found,
            }),
        }
    }

    fn int_bin(&mut self, op: Op, a: TermId, b: TermId) -> Result<TermId, IrError> {
        self.expect_int(a)?;
        self.expect_int(b)?;
        Ok(self.app(op, &[a, b], Sort::Int))
    }

    fn int_cmp(&mut self, op: Op, a: TermId, b: TermId) -> Result<TermId, IrError> {
        self.expect_int(a)?;
        self.expect_int(b)?;
        Ok(self.app(op, &[a, b], Sort::Bool))
    }

    /// Integer negation.
    ///
    /// # Errors
    ///
    /// Returns [`IrError::SortMismatch`] unless `a` is an integer.
    pub fn int_neg(&mut self, a: TermId) -> Result<TermId, IrError> {
        self.expect_int(a)?;
        Ok(self.app(Op::IntNeg, &[a], Sort::Int))
    }

    /// Integer addition.
    ///
    /// # Errors
    ///
    /// Returns [`IrError::SortMismatch`] unless both operands are integers.
    pub fn int_add(&mut self, a: TermId, b: TermId) -> Result<TermId, IrError> {
        self.int_bin(Op::IntAdd, a, b)
    }

    /// Integer subtraction.
    ///
    /// # Errors
    ///
    /// Returns [`IrError::SortMismatch`] unless both operands are integers.
    pub fn int_sub(&mut self, a: TermId, b: TermId) -> Result<TermId, IrError> {
        self.int_bin(Op::IntSub, a, b)
    }

    /// Integer multiplication (linear use is a fragment property, not enforced
    /// at build time).
    ///
    /// # Errors
    ///
    /// Returns [`IrError::SortMismatch`] unless both operands are integers.
    pub fn int_mul(&mut self, a: TermId, b: TermId) -> Result<TermId, IrError> {
        self.int_bin(Op::IntMul, a, b)
    }

    /// Integer Euclidean division (SMT-LIB `div`): `0 ≤ (mod a b) < |b|` for
    /// `b ≠ 0`, with the in-tree convention `div a 0 = 0`.
    ///
    /// # Errors
    ///
    /// Returns [`IrError::SortMismatch`] unless both operands are integers.
    pub fn int_div(&mut self, a: TermId, b: TermId) -> Result<TermId, IrError> {
        self.int_bin(Op::IntDiv, a, b)
    }

    /// Integer Euclidean modulo (SMT-LIB `mod`): always in `0..|b|` for `b ≠ 0`,
    /// with the convention `mod a 0 = a`.
    ///
    /// # Errors
    ///
    /// Returns [`IrError::SortMismatch`] unless both operands are integers.
    pub fn int_mod(&mut self, a: TermId, b: TermId) -> Result<TermId, IrError> {
        self.int_bin(Op::IntMod, a, b)
    }

    /// Integer absolute value (SMT-LIB `abs`).
    ///
    /// # Errors
    ///
    /// Returns [`IrError::SortMismatch`] unless `a` is an integer.
    pub fn int_abs(&mut self, a: TermId) -> Result<TermId, IrError> {
        self.expect_int(a)?;
        Ok(self.app(Op::IntAbs, &[a], Sort::Int))
    }

    /// SMT-LIB `(_ divisible n) x` — true iff `n` divides `x`. Sugar for
    /// `mod x n = 0` (result sort `Bool`); reuses the Euclidean [`Op::IntMod`].
    ///
    /// # Errors
    ///
    /// Returns [`IrError::SortMismatch`] unless `x` is an integer.
    pub fn int_divisible(&mut self, x: TermId, n: i128) -> Result<TermId, IrError> {
        let n_c = self.int_const(n);
        let m = self.int_mod(x, n_c)?;
        let zero = self.int_const(0);
        self.eq(m, zero)
    }

    /// Integer less-than (result sort `Bool`).
    ///
    /// # Errors
    ///
    /// Returns [`IrError::SortMismatch`] unless both operands are integers.
    pub fn int_lt(&mut self, a: TermId, b: TermId) -> Result<TermId, IrError> {
        self.int_cmp(Op::IntLt, a, b)
    }

    /// Integer less-or-equal (result sort `Bool`).
    ///
    /// # Errors
    ///
    /// Returns [`IrError::SortMismatch`] unless both operands are integers.
    pub fn int_le(&mut self, a: TermId, b: TermId) -> Result<TermId, IrError> {
        self.int_cmp(Op::IntLe, a, b)
    }

    /// Integer greater-than (result sort `Bool`).
    ///
    /// # Errors
    ///
    /// Returns [`IrError::SortMismatch`] unless both operands are integers.
    pub fn int_gt(&mut self, a: TermId, b: TermId) -> Result<TermId, IrError> {
        self.int_cmp(Op::IntGt, a, b)
    }

    /// Integer greater-or-equal (result sort `Bool`).
    ///
    /// # Errors
    ///
    /// Returns [`IrError::SortMismatch`] unless both operands are integers.
    pub fn int_ge(&mut self, a: TermId, b: TermId) -> Result<TermId, IrError> {
        self.int_cmp(Op::IntGe, a, b)
    }

    // ----- linear real arithmetic (ADR-0015) ----------------------------

    /// A real constant from an exact rational.
    pub fn real_const(&mut self, value: crate::rational::Rational) -> TermId {
        self.intern_node(TermNode::RealConst(value), Sort::Real)
    }

    /// A real constant `num/den`.
    ///
    /// # Panics
    ///
    /// Panics if `den` is zero (see [`crate::Rational::new`]).
    pub fn real_ratio(&mut self, num: i128, den: i128) -> TermId {
        self.real_const(crate::rational::Rational::new(num, den))
    }

    /// Declares a real symbol and returns its variable term.
    ///
    /// # Errors
    ///
    /// Returns [`IrError::SymbolSortConflict`] on a name reuse with a different
    /// sort.
    pub fn real_var(&mut self, name: &str) -> Result<TermId, IrError> {
        let s = self.declare(name, Sort::Real)?;
        Ok(self.var(s))
    }

    fn expect_real(&self, t: TermId) -> Result<(), IrError> {
        match self.sort_of(t) {
            Sort::Real => Ok(()),
            found @ (Sort::Bool
            | Sort::BitVec(_)
            | Sort::Array { .. }
            | Sort::Int
            | Sort::Datatype(_)) => Err(IrError::SortMismatch {
                expected: "Real",
                found,
            }),
        }
    }

    fn real_bin(&mut self, op: Op, a: TermId, b: TermId) -> Result<TermId, IrError> {
        self.expect_real(a)?;
        self.expect_real(b)?;
        Ok(self.app(op, &[a, b], Sort::Real))
    }

    fn real_cmp(&mut self, op: Op, a: TermId, b: TermId) -> Result<TermId, IrError> {
        self.expect_real(a)?;
        self.expect_real(b)?;
        Ok(self.app(op, &[a, b], Sort::Bool))
    }

    /// Real negation.
    ///
    /// # Errors
    ///
    /// Returns [`IrError::SortMismatch`] unless `a` is a real.
    pub fn real_neg(&mut self, a: TermId) -> Result<TermId, IrError> {
        self.expect_real(a)?;
        Ok(self.app(Op::RealNeg, &[a], Sort::Real))
    }

    /// Real addition.
    ///
    /// # Errors
    ///
    /// Returns [`IrError::SortMismatch`] unless both operands are reals.
    pub fn real_add(&mut self, a: TermId, b: TermId) -> Result<TermId, IrError> {
        self.real_bin(Op::RealAdd, a, b)
    }

    /// Real subtraction.
    ///
    /// # Errors
    ///
    /// Returns [`IrError::SortMismatch`] unless both operands are reals.
    pub fn real_sub(&mut self, a: TermId, b: TermId) -> Result<TermId, IrError> {
        self.real_bin(Op::RealSub, a, b)
    }

    /// Real multiplication (linear use is a fragment property, not enforced at
    /// build time).
    ///
    /// # Errors
    ///
    /// Returns [`IrError::SortMismatch`] unless both operands are reals.
    pub fn real_mul(&mut self, a: TermId, b: TermId) -> Result<TermId, IrError> {
        self.real_bin(Op::RealMul, a, b)
    }

    /// Real division (`/`). Total; the evaluator uses `x / 0 = 0`.
    ///
    /// # Errors
    ///
    /// Returns [`IrError::SortMismatch`] unless both operands are reals.
    pub fn real_div(&mut self, a: TermId, b: TermId) -> Result<TermId, IrError> {
        self.real_bin(Op::RealDiv, a, b)
    }

    /// Real less-than (result sort `Bool`).
    ///
    /// # Errors
    ///
    /// Returns [`IrError::SortMismatch`] unless both operands are reals.
    pub fn real_lt(&mut self, a: TermId, b: TermId) -> Result<TermId, IrError> {
        self.real_cmp(Op::RealLt, a, b)
    }

    /// Real less-or-equal (result sort `Bool`).
    ///
    /// # Errors
    ///
    /// Returns [`IrError::SortMismatch`] unless both operands are reals.
    pub fn real_le(&mut self, a: TermId, b: TermId) -> Result<TermId, IrError> {
        self.real_cmp(Op::RealLe, a, b)
    }

    /// Real greater-than (result sort `Bool`).
    ///
    /// # Errors
    ///
    /// Returns [`IrError::SortMismatch`] unless both operands are reals.
    pub fn real_gt(&mut self, a: TermId, b: TermId) -> Result<TermId, IrError> {
        self.real_cmp(Op::RealGt, a, b)
    }

    /// Real greater-or-equal (result sort `Bool`).
    ///
    /// # Errors
    ///
    /// Returns [`IrError::SortMismatch`] unless both operands are reals.
    pub fn real_ge(&mut self, a: TermId, b: TermId) -> Result<TermId, IrError> {
        self.real_cmp(Op::RealGe, a, b)
    }

    // ----- quantifiers (ADR-0016) ---------------------------------------

    /// Universal quantifier `forall var. body`, binding the declared symbol
    /// `var` over the `Bool` `body`.
    ///
    /// # Errors
    ///
    /// Returns [`IrError::SortMismatch`] unless `body` is `Bool`.
    ///
    /// # Panics
    ///
    /// Panics if `var` does not belong to this arena.
    pub fn forall(&mut self, var: SymbolId, body: TermId) -> Result<TermId, IrError> {
        self.expect_bool(body)?;
        let _ = self.symbols[var.index()];
        Ok(self.app(Op::Forall(var), &[body], Sort::Bool))
    }

    /// Existential quantifier `exists var. body`, binding the declared symbol
    /// `var` over the `Bool` `body`.
    ///
    /// # Errors
    ///
    /// Returns [`IrError::SortMismatch`] unless `body` is `Bool`.
    ///
    /// # Panics
    ///
    /// Panics if `var` does not belong to this arena.
    pub fn exists(&mut self, var: SymbolId, body: TermId) -> Result<TermId, IrError> {
        self.expect_bool(body)?;
        let _ = self.symbols[var.index()];
        Ok(self.app(Op::Exists(var), &[body], Sort::Bool))
    }
}

fn check_width(width: u32) -> Result<(), IrError> {
    if width == 0 || width > MAX_BV_WIDTH {
        return Err(IrError::InvalidWidth(width));
    }
    Ok(())
}

/// Validates a function-signature sort: only finite scalar sorts
/// (`Bool`/`BitVec`) are allowed. Arrays and integers are rejected (functions
/// over integers are not in the bit-blasted fragment yet, ADR-0014).
fn check_scalar_width(sort: Sort) -> Result<(), IrError> {
    match sort {
        Sort::Bool => Ok(()),
        Sort::BitVec(w) => check_width(w),
        found @ (Sort::Array { .. } | Sort::Int | Sort::Real | Sort::Datatype(_)) => {
            Err(IrError::SortMismatch {
                expected: "Bool or BitVec",
                found,
            })
        }
    }
}

fn checked_output_width(base: u32, extra: u32) -> Result<u32, IrError> {
    let out = base.saturating_add(extra);
    if out > MAX_BV_WIDTH {
        return Err(IrError::ConcatTooWide(out));
    }
    Ok(out)
}
