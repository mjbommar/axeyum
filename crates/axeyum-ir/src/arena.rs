//! The term arena: interned storage plus typed, sort-checked builders.

use std::collections::HashMap;

use crate::error::IrError;
use crate::sort::{MAX_BV_WIDTH, Sort, mask};
use crate::term::{Op, SymbolId, TermId, TermNode};

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
    nodes: Vec<TermNode>,
    sorts: Vec<Sort>,
    intern: HashMap<TermNode, TermId>,
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
            found @ Sort::BitVec(_) => Err(IrError::SortMismatch {
                expected: "Bool",
                found,
            }),
        }
    }

    fn expect_bv(&self, t: TermId) -> Result<u32, IrError> {
        match self.sort_of(t) {
            Sort::BitVec(w) => Ok(w),
            found @ Sort::Bool => Err(IrError::SortMismatch {
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
        let out = wa + wb;
        if out > MAX_BV_WIDTH {
            return Err(IrError::ConcatTooWide(out));
        }
        Ok(self.app(Op::Concat, &[a, b], Sort::BitVec(out)))
    }
}

fn check_width(width: u32) -> Result<(), IrError> {
    if width == 0 || width > MAX_BV_WIDTH {
        return Err(IrError::InvalidWidth(width));
    }
    Ok(())
}
