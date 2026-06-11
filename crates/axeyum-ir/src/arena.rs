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

    /// Zero extension by `by` bits.
    ///
    /// # Errors
    ///
    /// Returns [`IrError::SortMismatch`] unless `a` is a bit-vector, or
    /// [`IrError::ConcatTooWide`] if the result exceeds [`MAX_BV_WIDTH`].
    pub fn zero_ext(&mut self, by: u32, a: TermId) -> Result<TermId, IrError> {
        let w = self.expect_bv(a)?;
        let out = w + by;
        if out > MAX_BV_WIDTH {
            return Err(IrError::ConcatTooWide(out));
        }
        Ok(self.app(Op::ZeroExt { by }, &[a], Sort::BitVec(out)))
    }

    /// Sign extension by `by` bits.
    ///
    /// # Errors
    ///
    /// Same conditions as [`TermArena::zero_ext`].
    pub fn sign_ext(&mut self, by: u32, a: TermId) -> Result<TermId, IrError> {
        let w = self.expect_bv(a)?;
        let out = w + by;
        if out > MAX_BV_WIDTH {
            return Err(IrError::ConcatTooWide(out));
        }
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
}

fn check_width(width: u32) -> Result<(), IrError> {
    if width == 0 || width > MAX_BV_WIDTH {
        return Err(IrError::InvalidWidth(width));
    }
    Ok(())
}
