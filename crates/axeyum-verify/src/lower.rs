//! Symbolic lowering of the restricted-Rust AST into `axeyum-ir` terms, with the
//! panic classes turned into explicit *bad-state* boolean terms.
//!
//! The interpreter walks the body once, maintaining a symbolic environment
//! (name → term) and a *path condition*. At every panic class (overflow,
//! `÷0`/`%0`, index-out-of-bounds, `assert!` false, `panic!` reached,
//! `unwrap`-on-`None`) it records `path_condition ∧ <bad predicate>` as a bad
//! state. The verifier then asks the solver whether **any** bad state is
//! reachable: a model is a concrete bug witness; `unsat` is a bounded proof of
//! safety.
//!
//! Soundness posture: BV division is SMT-LIB-total (`bvudiv x 0 = all-ones`),
//! which is *not* Rust's panic — so `/` and `%` emit an explicit `divisor == 0`
//! bad state rather than relying on the operator. Overflow uses the IR's
//! `bv_{u,s}{add,sub,mul}o` predicates, matching Rust's debug-mode panics with
//! the operand signedness.

use std::collections::HashMap;

use axeyum_ir::{SymbolId, TermArena, TermId};

use crate::ast::{ArrayParam, BinOp, Expr, Param, Program, Stmt, Ty, UnOp};

/// Why a lowering could not proceed (an out-of-fragment construct or a body the
/// front-end accepted but the runtime cannot model). Surfaced as `Unknown`,
/// never as a wrong verdict.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LowerError {
    /// A referenced name was not a known parameter / binding.
    UnknownVar(String),
    /// A type mismatch the front-end did not catch (e.g. bool where int needed).
    TypeError(String),
    /// A construct outside the supported fragment.
    Unsupported(String),
}

impl std::fmt::Display for LowerError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            LowerError::UnknownVar(n) => write!(f, "unknown variable `{n}`"),
            LowerError::TypeError(m) => write!(f, "type error: {m}"),
            LowerError::Unsupported(m) => write!(f, "unsupported construct: {m}"),
        }
    }
}

impl std::error::Error for LowerError {}

/// A symbolic value: a term plus its scalar type (so operators pick the right
/// signed/unsigned IR builder).
#[derive(Clone, Copy)]
struct SymVal {
    term: TermId,
    ty: Ty,
}

/// A discovered potential bug: a human-readable class label plus the boolean
/// term that is satisfiable exactly when the bug is reachable.
pub struct BadState {
    /// A short label, e.g. `"add overflow"` or `"assert! violated"`.
    pub label: String,
    /// `path_condition ∧ bad_predicate`: sat ⇒ reachable bug.
    pub term: TermId,
}

/// The fully-lowered program: the input symbols (for model lifting) and the list
/// of reachable-bug terms.
pub struct Lowered {
    /// Scalar input symbols, in `Program::params` order.
    pub param_syms: Vec<(String, SymbolId, Ty)>,
    /// Array element symbols, in `Program::arrays` order (`name`, elems, ty).
    pub array_syms: Vec<(String, Vec<SymbolId>, Ty)>,
    /// All bad states discovered along all paths.
    pub bad_states: Vec<BadState>,
}

/// The walking interpreter.
struct Lowerer<'a> {
    arena: &'a mut TermArena,
    /// name → current symbolic value.
    env: HashMap<String, SymVal>,
    /// array name → (element terms, element type).
    arrays: HashMap<String, (Vec<TermId>, Ty)>,
    /// The current conjunction of branch conditions (the path condition).
    path: Vec<TermId>,
    /// Discovered bad states.
    bad_states: Vec<BadState>,
    /// A stack of the names `let`-declared in each currently-open lexical scope
    /// (an `if`/`else` arm or loop body). A fresh `let` inside an arm shadows any
    /// outer binding only *within* that arm; on leaving the arm the outer value
    /// is restored (the runtime `env` is flat, so without this an arm-local
    /// shadow would leak through the join as a reassignment — a spurious bug).
    scopes: Vec<Vec<String>>,
}

impl Lowerer<'_> {
    fn truth(&mut self) -> TermId {
        self.arena.bool_const(true)
    }

    /// `AND` of the current path condition (true when empty).
    fn path_term(&mut self) -> Result<TermId, LowerError> {
        let mut acc = self.truth();
        let conds: Vec<TermId> = self.path.clone();
        for c in conds {
            acc = self.arena.and(acc, c).map_err(|e| ir(&e))?;
        }
        Ok(acc)
    }

    /// Record `path ∧ pred` as a reachable bad state under `label`.
    fn record(&mut self, label: &str, pred: TermId) -> Result<(), LowerError> {
        let p = self.path_term()?;
        let term = self.arena.and(p, pred).map_err(|e| ir(&e))?;
        self.bad_states.push(BadState {
            label: label.to_string(),
            term,
        });
        Ok(())
    }

    // --- expression lowering -------------------------------------------------

    fn lower_expr(&mut self, e: &Expr) -> Result<SymVal, LowerError> {
        match e {
            Expr::IntLit { value, ty } => {
                let width = ty
                    .width()
                    .ok_or_else(|| LowerError::TypeError("int literal with bool type".into()))?;
                let term = self.arena.bv_const(width, *value).map_err(|e| ir(&e))?;
                Ok(SymVal { term, ty: *ty })
            }
            Expr::BoolLit(b) => {
                let term = self.arena.bool_const(*b);
                Ok(SymVal { term, ty: Ty::Bool })
            }
            Expr::Var(name) => self
                .env
                .get(name)
                .copied()
                .ok_or_else(|| LowerError::UnknownVar(name.clone())),
            Expr::Unary { op, operand } => self.lower_unary(*op, operand),
            Expr::Binary { op, lhs, rhs } => self.lower_binary(*op, lhs, rhs),
            Expr::Ite { cond, then, els } => {
                let c = self.lower_expr(cond)?;
                expect_bool(c, "if-expression condition")?;
                let t = self.lower_expr(then)?;
                let f = self.lower_expr(els)?;
                if t.ty != f.ty {
                    return Err(LowerError::TypeError(
                        "if/else arms have different types".into(),
                    ));
                }
                let term = self.arena.ite(c.term, t.term, f.term).map_err(|e| ir(&e))?;
                Ok(SymVal { term, ty: t.ty })
            }
            Expr::Overflows { op, lhs, rhs } => {
                let a = self.lower_expr(lhs)?;
                let b = self.lower_expr(rhs)?;
                if a.ty != b.ty {
                    return Err(LowerError::TypeError(
                        "overflow check on differing operand types".into(),
                    ));
                }
                let signed = a.ty.is_signed();
                let term = match (op, signed) {
                    (BinOp::Add, true) => self.arena.bv_saddo(a.term, b.term),
                    (BinOp::Add, false) => self.arena.bv_uaddo(a.term, b.term),
                    (BinOp::Sub, true) => self.arena.bv_ssubo(a.term, b.term),
                    (BinOp::Sub, false) => self.arena.bv_usubo(a.term, b.term),
                    (BinOp::Mul, true) => self.arena.bv_smulo(a.term, b.term),
                    (BinOp::Mul, false) => self.arena.bv_umulo(a.term, b.term),
                    _ => {
                        return Err(LowerError::TypeError(
                            "overflow check only defined for +/-/*".into(),
                        ));
                    }
                }
                .map_err(|e| ir(&e))?;
                // The result is a bool (whether the op overflows).
                Ok(SymVal {
                    term,
                    ty: Ty::Bool,
                })
            }
            Expr::Index { array, index, ty } => self.lower_index(array, index, *ty),
            Expr::UnwrapOption { is_some, value } => {
                // Reaching the unwrap with `is_some == false` is the bug (the
                // `None` branch). Record it; the value flows through regardless.
                let disc = self.lower_expr(is_some)?;
                expect_bool(disc, "Option discriminant")?;
                let none = self.arena.not(disc.term).map_err(|e| ir(&e))?;
                self.record("unwrap on None", none)?;
                self.lower_expr(value)
            }
        }
    }

    fn lower_unary(&mut self, op: UnOp, operand: &Expr) -> Result<SymVal, LowerError> {
        let v = self.lower_expr(operand)?;
        match op {
            UnOp::Not => match v.ty {
                Ty::Bool => {
                    let term = self.arena.not(v.term).map_err(|e| ir(&e))?;
                    Ok(SymVal { term, ty: Ty::Bool })
                }
                Ty::Int { .. } => {
                    let term = self.arena.bv_not(v.term).map_err(|e| ir(&e))?;
                    Ok(SymVal { term, ty: v.ty })
                }
            },
            UnOp::Neg => {
                if !matches!(v.ty, Ty::Int { signed: true, .. }) {
                    return Err(LowerError::TypeError(
                        "unary negation only on signed integers".into(),
                    ));
                }
                // iN::MIN negation overflows (panics in debug).
                let ovf = self.arena.bv_nego(v.term).map_err(|e| ir(&e))?;
                self.record("negation overflow", ovf)?;
                let term = self.arena.bv_neg(v.term).map_err(|e| ir(&e))?;
                Ok(SymVal { term, ty: v.ty })
            }
        }
    }

    #[allow(clippy::too_many_lines)]
    fn lower_binary(&mut self, op: BinOp, lhs: &Expr, rhs: &Expr) -> Result<SymVal, LowerError> {
        let a = self.lower_expr(lhs)?;
        let b = self.lower_expr(rhs)?;
        // Boolean connectives.
        match op {
            BinOp::And => {
                expect_bool(a, "&& lhs")?;
                expect_bool(b, "&& rhs")?;
                let term = self.arena.and(a.term, b.term).map_err(|e| ir(&e))?;
                return Ok(SymVal { term, ty: Ty::Bool });
            }
            BinOp::Or => {
                expect_bool(a, "|| lhs")?;
                expect_bool(b, "|| rhs")?;
                let term = self.arena.or(a.term, b.term).map_err(|e| ir(&e))?;
                return Ok(SymVal { term, ty: Ty::Bool });
            }
            _ => {}
        }
        // Comparisons / equality produce a bool.
        if let Some(term) = self.lower_compare(op, a, b)? {
            return Ok(SymVal { term, ty: Ty::Bool });
        }
        // Arithmetic / bitwise on integers (same width + signedness).
        if a.ty != b.ty {
            return Err(LowerError::TypeError(format!(
                "binary op operands differ in type: {:?} vs {:?}",
                a.ty, b.ty
            )));
        }
        let signed = a.ty.is_signed();
        let term = match op {
            BinOp::Add => {
                let ovf = if signed {
                    self.arena.bv_saddo(a.term, b.term)
                } else {
                    self.arena.bv_uaddo(a.term, b.term)
                }
                .map_err(|e| ir(&e))?;
                self.record("add overflow", ovf)?;
                self.arena.bv_add(a.term, b.term).map_err(|e| ir(&e))?
            }
            BinOp::Sub => {
                let ovf = if signed {
                    self.arena.bv_ssubo(a.term, b.term)
                } else {
                    self.arena.bv_usubo(a.term, b.term)
                }
                .map_err(|e| ir(&e))?;
                self.record("sub overflow", ovf)?;
                self.arena.bv_sub(a.term, b.term).map_err(|e| ir(&e))?
            }
            BinOp::Mul => {
                let ovf = if signed {
                    self.arena.bv_smulo(a.term, b.term)
                } else {
                    self.arena.bv_umulo(a.term, b.term)
                }
                .map_err(|e| ir(&e))?;
                self.record("mul overflow", ovf)?;
                self.arena.bv_mul(a.term, b.term).map_err(|e| ir(&e))?
            }
            BinOp::Div => {
                self.record_div_zero("division by zero", b)?;
                if signed {
                    // Rust also panics on `iN::MIN / -1` (the quotient overflows);
                    // BV `sdiv` is total, so check it explicitly.
                    self.record_sdiv_overflow(a, b)?;
                    self.arena.bv_sdiv(a.term, b.term)
                } else {
                    self.arena.bv_udiv(a.term, b.term)
                }
                .map_err(|e| ir(&e))?
            }
            BinOp::Rem => {
                self.record_div_zero("remainder by zero", b)?;
                if signed {
                    self.arena.bv_srem(a.term, b.term)
                } else {
                    self.arena.bv_urem(a.term, b.term)
                }
                .map_err(|e| ir(&e))?
            }
            // Wrapping arithmetic: the same total BV op, but with no overflow
            // panic class recorded (this is exactly Rust's modular semantics).
            BinOp::WrappingAdd => self.arena.bv_add(a.term, b.term).map_err(|e| ir(&e))?,
            BinOp::WrappingSub => self.arena.bv_sub(a.term, b.term).map_err(|e| ir(&e))?,
            BinOp::WrappingMul => self.arena.bv_mul(a.term, b.term).map_err(|e| ir(&e))?,
            // Saturating arithmetic: clamp to the type bound on overflow (no panic).
            BinOp::SaturatingAdd | BinOp::SaturatingSub | BinOp::SaturatingMul => {
                self.lower_saturating(op, a, b)?
            }
            // `min`/`max`: select an operand by a signedness-correct comparison.
            BinOp::Min | BinOp::Max => {
                let cmp = match (op, signed) {
                    (BinOp::Min, true) => self.arena.bv_sle(a.term, b.term),
                    (BinOp::Min, false) => self.arena.bv_ule(a.term, b.term),
                    (BinOp::Max, true) => self.arena.bv_sge(a.term, b.term),
                    (BinOp::Max, false) => self.arena.bv_uge(a.term, b.term),
                    _ => unreachable!(),
                }
                .map_err(|e| ir(&e))?;
                self.arena.ite(cmp, a.term, b.term).map_err(|e| ir(&e))?
            }
            BinOp::BitAnd => self.arena.bv_and(a.term, b.term).map_err(|e| ir(&e))?,
            BinOp::BitOr => self.arena.bv_or(a.term, b.term).map_err(|e| ir(&e))?,
            BinOp::BitXor => self.arena.bv_xor(a.term, b.term).map_err(|e| ir(&e))?,
            BinOp::Shl => self.arena.bv_shl(a.term, b.term).map_err(|e| ir(&e))?,
            BinOp::Shr => {
                if signed {
                    self.arena.bv_ashr(a.term, b.term).map_err(|e| ir(&e))?
                } else {
                    self.arena.bv_lshr(a.term, b.term).map_err(|e| ir(&e))?
                }
            }
            BinOp::And | BinOp::Or => unreachable!("handled above"),
            BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge => {
                unreachable!("handled by lower_compare")
            }
        };
        Ok(SymVal { term, ty: a.ty })
    }

    /// Comparisons + equality; `None` if `op` is not a comparison.
    fn lower_compare(
        &mut self,
        op: BinOp,
        a: SymVal,
        b: SymVal,
    ) -> Result<Option<TermId>, LowerError> {
        if a.ty != b.ty {
            // Equality of mismatched types is a front-end error; only flag for
            // the comparison ops (others fall through to `None`).
            if matches!(
                op,
                BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge
            ) {
                return Err(LowerError::TypeError(
                    "comparison of differing types".into(),
                ));
            }
            return Ok(None);
        }
        let signed = a.ty.is_signed();
        let term = match op {
            BinOp::Eq => self.arena.eq(a.term, b.term).map_err(|e| ir(&e))?,
            BinOp::Ne => {
                let eq = self.arena.eq(a.term, b.term).map_err(|e| ir(&e))?;
                self.arena.not(eq).map_err(|e| ir(&e))?
            }
            BinOp::Lt if signed => self.arena.bv_slt(a.term, b.term).map_err(|e| ir(&e))?,
            BinOp::Le if signed => self.arena.bv_sle(a.term, b.term).map_err(|e| ir(&e))?,
            BinOp::Gt if signed => self.arena.bv_sgt(a.term, b.term).map_err(|e| ir(&e))?,
            BinOp::Ge if signed => self.arena.bv_sge(a.term, b.term).map_err(|e| ir(&e))?,
            BinOp::Lt => self.arena.bv_ult(a.term, b.term).map_err(|e| ir(&e))?,
            BinOp::Le => self.arena.bv_ule(a.term, b.term).map_err(|e| ir(&e))?,
            BinOp::Gt => self.arena.bv_ugt(a.term, b.term).map_err(|e| ir(&e))?,
            BinOp::Ge => self.arena.bv_uge(a.term, b.term).map_err(|e| ir(&e))?,
            _ => return Ok(None),
        };
        Ok(Some(term))
    }

    /// Records `path ∧ divisor == 0` for `/` and `%` (BV div is total, so we
    /// check the Rust panic explicitly). The divisor is the already-lowered
    /// right operand (re-lowering would double-count its panic classes).
    fn record_div_zero(&mut self, label: &str, divisor: SymVal) -> Result<(), LowerError> {
        let width = divisor
            .ty
            .width()
            .ok_or_else(|| LowerError::TypeError("division by a bool".into()))?;
        let zero = self.arena.bv_const(width, 0).map_err(|e| ir(&e))?;
        let is_zero = self.arena.eq(divisor.term, zero).map_err(|e| ir(&e))?;
        self.record(label, is_zero)
    }

    /// Records `path ∧ a == iN::MIN ∧ b == -1` for signed `/` — the Rust
    /// division-overflow panic (`bv_sdiv` is total, so we check it explicitly).
    fn record_sdiv_overflow(&mut self, a: SymVal, b: SymVal) -> Result<(), LowerError> {
        let width =
            a.ty.width()
                .ok_or_else(|| LowerError::TypeError("signed division on a bool".into()))?;
        // iN::MIN bit pattern = 1 << (width-1); -1 = all ones.
        let min_pat = 1u128 << (width - 1);
        let neg_one_pat = if width == 128 {
            u128::MAX
        } else {
            (1u128 << width) - 1
        };
        let min = self.arena.bv_const(width, min_pat).map_err(|e| ir(&e))?;
        let neg_one = self
            .arena
            .bv_const(width, neg_one_pat)
            .map_err(|e| ir(&e))?;
        let a_is_min = self.arena.eq(a.term, min).map_err(|e| ir(&e))?;
        let b_is_neg1 = self.arena.eq(b.term, neg_one).map_err(|e| ir(&e))?;
        let ovf = self.arena.and(a_is_min, b_is_neg1).map_err(|e| ir(&e))?;
        self.record("signed division overflow (MIN / -1)", ovf)
    }

    /// Saturating arithmetic: `ite(overflow, clamp, base)` where `base` is the
    /// total BV op and `clamp` is the type bound the result saturates to. No
    /// panic class is recorded — saturating ops never panic. The overflow
    /// predicates (`bv_*addo`/`*subo`/`*mulo`) are the same ones the checked ops
    /// use, so this is exact w.r.t. Rust's `saturating_*` semantics.
    fn lower_saturating(
        &mut self,
        op: BinOp,
        a: SymVal,
        b: SymVal,
    ) -> Result<TermId, LowerError> {
        let width =
            a.ty.width()
                .ok_or_else(|| LowerError::TypeError("saturating op on a bool".into()))?;
        let signed = a.ty.is_signed();
        let all_ones = if width == 128 {
            u128::MAX
        } else {
            (1u128 << width) - 1
        };
        let (base, ovf) = match op {
            BinOp::SaturatingAdd => (
                self.arena.bv_add(a.term, b.term).map_err(|e| ir(&e))?,
                if signed {
                    self.arena.bv_saddo(a.term, b.term)
                } else {
                    self.arena.bv_uaddo(a.term, b.term)
                }
                .map_err(|e| ir(&e))?,
            ),
            BinOp::SaturatingSub => (
                self.arena.bv_sub(a.term, b.term).map_err(|e| ir(&e))?,
                if signed {
                    self.arena.bv_ssubo(a.term, b.term)
                } else {
                    self.arena.bv_usubo(a.term, b.term)
                }
                .map_err(|e| ir(&e))?,
            ),
            BinOp::SaturatingMul => (
                self.arena.bv_mul(a.term, b.term).map_err(|e| ir(&e))?,
                if signed {
                    self.arena.bv_smulo(a.term, b.term)
                } else {
                    self.arena.bv_umulo(a.term, b.term)
                }
                .map_err(|e| ir(&e))?,
            ),
            _ => unreachable!("lower_saturating only handles saturating ops"),
        };
        let clamp = if signed {
            // Signed bound: MAX = 0b0111..1, MIN = 0b1000..0. On overflow the
            // result saturates to MAX when the (would-be) result is positive,
            // else MIN. For add/sub that is decided by `a`'s sign; for mul by
            // whether the operands share a sign.
            let maxv = self
                .arena
                .bv_const(width, (1u128 << (width - 1)) - 1)
                .map_err(|e| ir(&e))?;
            let minv = self
                .arena
                .bv_const(width, 1u128 << (width - 1))
                .map_err(|e| ir(&e))?;
            let zero = self.arena.bv_const(width, 0).map_err(|e| ir(&e))?;
            let a_nonneg = self.arena.bv_sge(a.term, zero).map_err(|e| ir(&e))?;
            if matches!(op, BinOp::SaturatingMul) {
                let b_nonneg = self.arena.bv_sge(b.term, zero).map_err(|e| ir(&e))?;
                let not_a = self.arena.not(a_nonneg).map_err(|e| ir(&e))?;
                let not_b = self.arena.not(b_nonneg).map_err(|e| ir(&e))?;
                let both_pos = self.arena.and(a_nonneg, b_nonneg).map_err(|e| ir(&e))?;
                let both_neg = self.arena.and(not_a, not_b).map_err(|e| ir(&e))?;
                let same_sign = self.arena.or(both_pos, both_neg).map_err(|e| ir(&e))?;
                self.arena.ite(same_sign, maxv, minv).map_err(|e| ir(&e))?
            } else {
                self.arena.ite(a_nonneg, maxv, minv).map_err(|e| ir(&e))?
            }
        } else if matches!(op, BinOp::SaturatingSub) {
            // Unsigned underflow saturates to 0; add/mul overflow to all-ones.
            self.arena.bv_const(width, 0).map_err(|e| ir(&e))?
        } else {
            self.arena.bv_const(width, all_ones).map_err(|e| ir(&e))?
        };
        self.arena.ite(ovf, clamp, base).map_err(|e| ir(&e))
    }

    /// `arr[idx]`: records `idx >= len` as out-of-bounds, then returns a chained
    /// `ite` selecting the indexed element (defaulting to element 0 when OOB —
    /// the bad state already captures the panic, the value is don't-care).
    fn lower_index(&mut self, array: &str, index: &Expr, ty: Ty) -> Result<SymVal, LowerError> {
        let (elems, elem_ty) = self
            .arrays
            .get(array)
            .cloned()
            .ok_or_else(|| LowerError::UnknownVar(array.to_string()))?;
        if elem_ty != ty {
            return Err(LowerError::TypeError(format!(
                "index element type mismatch on `{array}`"
            )));
        }
        let idx = self.lower_expr(index)?;
        let iw = idx
            .ty
            .width()
            .ok_or_else(|| LowerError::TypeError("index is not an integer".into()))?;
        let len = u128::try_from(elems.len()).unwrap_or(u128::MAX);
        let len_t = self
            .arena
            .bv_const(iw, len & mask(iw))
            .map_err(|e| ir(&e))?;
        // Out of bounds iff idx >= len (unsigned).
        let oob = self.arena.bv_uge(idx.term, len_t).map_err(|e| ir(&e))?;
        self.record("index out of bounds", oob)?;
        // Build a chain: ite(idx==0, e0, ite(idx==1, e1, ... e_{n-1})).
        let mut acc = *elems.last().expect("array has >=1 element");
        for (k, &elem) in elems.iter().enumerate().rev().skip(1) {
            let k_t = self
                .arena
                .bv_const(iw, (k as u128) & mask(iw))
                .map_err(|e| ir(&e))?;
            let eqk = self.arena.eq(idx.term, k_t).map_err(|e| ir(&e))?;
            acc = self.arena.ite(eqk, elem, acc).map_err(|e| ir(&e))?;
        }
        Ok(SymVal {
            term: acc,
            ty: elem_ty,
        })
    }

    // --- statement lowering --------------------------------------------------

    fn lower_block(&mut self, body: &[Stmt]) -> Result<(), LowerError> {
        for s in body {
            self.lower_stmt(s)?;
        }
        Ok(())
    }

    /// Lower a block as a fresh lexical scope: any name `let`-declared *inside*
    /// `body` is local to it. After the block, a name that shadowed an outer
    /// binding (present in `outer`) is restored to its outer value; a name newly
    /// introduced (absent from `outer`) is removed. This keeps an arm-local `let`
    /// from leaking out as if it were a reassignment.
    fn lower_scoped(
        &mut self,
        body: &[Stmt],
        outer: &HashMap<String, SymVal>,
    ) -> Result<(), LowerError> {
        self.scopes.push(Vec::new());
        let result = self.lower_block(body);
        let declared = self.scopes.pop().unwrap_or_default();
        // Restore/remove even on the error path so the env stays consistent.
        for name in declared {
            match outer.get(&name) {
                Some(outer_val) => {
                    self.env.insert(name, *outer_val);
                }
                None => {
                    self.env.remove(&name);
                }
            }
        }
        result
    }

    fn lower_stmt(&mut self, s: &Stmt) -> Result<(), LowerError> {
        match s {
            Stmt::Let { name, ty, value } => {
                let v = self.lower_expr(value)?;
                if v.ty != *ty {
                    return Err(LowerError::TypeError(format!(
                        "let `{name}`: declared {ty:?} but initializer is {:?}",
                        v.ty
                    )));
                }
                if let Some(scope) = self.scopes.last_mut() {
                    scope.push(name.clone());
                }
                self.env.insert(name.clone(), v);
                Ok(())
            }
            Stmt::Assign { name, value } => {
                let v = self.lower_expr(value)?;
                let prev = self
                    .env
                    .get(name)
                    .ok_or_else(|| LowerError::UnknownVar(name.clone()))?;
                if prev.ty != v.ty {
                    return Err(LowerError::TypeError(format!(
                        "assignment to `{name}` changes type"
                    )));
                }
                self.env.insert(name.clone(), v);
                Ok(())
            }
            Stmt::If { cond, then, els } => {
                let c = self.lower_expr(cond)?;
                expect_bool(c, "if condition")?;
                let not_c = self.arena.not(c.term).map_err(|e| ir(&e))?;
                // Then-branch: snapshot env so assignments don't leak across arms;
                // values that must merge are recombined via ite below. Each arm is
                // a lexical scope: a fresh `let` inside it shadows an outer binding
                // only within the arm, so we restore shadowed outer values before
                // capturing the arm env (otherwise the shadow leaks through the
                // join — see the `if_merge` shadowing test).
                let env_before = self.env.clone();
                self.path.push(c.term);
                self.lower_scoped(then, &env_before)?;
                let env_then = std::mem::replace(&mut self.env, env_before.clone());
                self.path.pop();

                self.path.push(not_c);
                self.lower_scoped(els, &env_before)?;
                let env_else = std::mem::take(&mut self.env);
                self.path.pop();

                // Merge: for each name live in both, value = ite(c, then, else).
                self.env = self.merge_envs(c.term, &env_before, &env_then, &env_else)?;
                Ok(())
            }
            Stmt::Assert(cond) => {
                let c = self.lower_expr(cond)?;
                expect_bool(c, "assert! condition")?;
                let violated = self.arena.not(c.term).map_err(|e| ir(&e))?;
                self.record("assert! violated", violated)
            }
            Stmt::Panic => {
                let truth = self.truth();
                self.record("panic! reached", truth)
            }
            Stmt::Eval(e) => {
                self.lower_expr(e)?;
                Ok(())
            }
            Stmt::While { cond, bound, body } => {
                // Bounded model checking by unrolling: each of the `bound`
                // iterations is exactly `if cond { body }` evaluated in sequence.
                // Reusing `If` gives the correct env-merge (an iteration that does
                // not run leaves the bindings untouched) and accumulates the guard
                // `cond` into the path condition, so panic classes in `body` are
                // only flagged on feasible iterations. This is a *bounded*
                // guarantee (no bug within `bound` iterations), never a claim of
                // total correctness.
                for _ in 0..*bound {
                    self.lower_stmt(&Stmt::If {
                        cond: cond.clone(),
                        then: body.clone(),
                        els: Vec::new(),
                    })?;
                }
                Ok(())
            }
            Stmt::For {
                var,
                var_ty,
                bound,
                body,
            } => {
                let width = var_ty
                    .width()
                    .ok_or_else(|| LowerError::TypeError("loop var is not an integer".into()))?;
                for i in 0..*bound {
                    let it = self
                        .arena
                        .bv_const(width, i & mask(width))
                        .map_err(|e| ir(&e))?;
                    self.env.insert(
                        var.clone(),
                        SymVal {
                            term: it,
                            ty: *var_ty,
                        },
                    );
                    // The body is a lexical scope: a `let` inside it is local to
                    // the iteration (and must not leak as an outer shadow).
                    let outer = self.env.clone();
                    self.lower_scoped(body, &outer)?;
                }
                self.env.remove(var);
                Ok(())
            }
        }
    }

    /// Merges two branch environments at a join point: a name keeps its value if
    /// unchanged, else becomes `ite(cond, then_val, else_val)`.
    fn merge_envs(
        &mut self,
        cond: TermId,
        before: &HashMap<String, SymVal>,
        then_env: &HashMap<String, SymVal>,
        else_env: &HashMap<String, SymVal>,
    ) -> Result<HashMap<String, SymVal>, LowerError> {
        let mut merged = HashMap::new();
        for name in before.keys() {
            let t = then_env.get(name);
            let e = else_env.get(name);
            match (t, e) {
                (Some(tv), Some(ev)) if tv.term == ev.term => {
                    merged.insert(name.clone(), *tv);
                }
                (Some(tv), Some(ev)) if tv.ty == ev.ty => {
                    let term = self.arena.ite(cond, tv.term, ev.term).map_err(|e| ir(&e))?;
                    merged.insert(name.clone(), SymVal { term, ty: tv.ty });
                }
                _ => {
                    // Diverging types or missing on one side: keep the pre-branch
                    // value (a binding can't be redeclared with a new type in our
                    // fragment, so this is the unchanged value).
                    if let Some(bv) = before.get(name) {
                        merged.insert(name.clone(), *bv);
                    }
                }
            }
        }
        Ok(merged)
    }
}

fn expect_bool(v: SymVal, ctx: &str) -> Result<(), LowerError> {
    if matches!(v.ty, Ty::Bool) {
        Ok(())
    } else {
        Err(LowerError::TypeError(format!("{ctx} must be a bool")))
    }
}

fn ir(e: &axeyum_ir::IrError) -> LowerError {
    LowerError::Unsupported(format!("IR construction failed: {e}"))
}

fn mask(width: u32) -> u128 {
    if width >= 128 {
        u128::MAX
    } else {
        (1u128 << width) - 1
    }
}

/// Lowers a whole [`Program`] into its input symbols and reachable-bug terms.
///
/// # Errors
///
/// Returns a [`LowerError`] if the body references an unknown name, has a type
/// mismatch the front-end missed, or contains a construct the runtime cannot
/// model (surfaced as `Unknown` by the verifier, never a wrong verdict).
pub fn lower_program(arena: &mut TermArena, program: &Program) -> Result<Lowered, LowerError> {
    let mut env = HashMap::new();
    let mut param_syms = Vec::new();
    for Param { name, ty } in &program.params {
        let sym = declare_scalar(arena, name, *ty)?;
        let term = arena.var(sym);
        env.insert(name.clone(), SymVal { term, ty: *ty });
        param_syms.push((name.clone(), sym, *ty));
    }

    let mut arrays = HashMap::new();
    let mut array_syms = Vec::new();
    for ArrayParam { name, elem, len } in &program.arrays {
        let mut syms = Vec::new();
        let mut terms = Vec::new();
        for k in 0..*len {
            let sym = declare_scalar(arena, &format!("{name}[{k}]"), *elem)?;
            syms.push(sym);
            terms.push(arena.var(sym));
        }
        if terms.is_empty() {
            return Err(LowerError::Unsupported(format!(
                "array `{name}` has length 0 (no element to index)"
            )));
        }
        arrays.insert(name.clone(), (terms, *elem));
        array_syms.push((name.clone(), syms, *elem));
    }

    let mut lowerer = Lowerer {
        arena,
        env,
        arrays,
        path: Vec::new(),
        bad_states: Vec::new(),
        scopes: Vec::new(),
    };
    lowerer.lower_block(&program.body)?;

    Ok(Lowered {
        param_syms,
        array_syms,
        bad_states: lowerer.bad_states,
    })
}

/// The result of lowering one pure scalar expression against a supplied
/// environment: the value term, its type, and any panic-class bad predicates the
/// expression itself contributes (overflow, `÷0`/`%0`), each as a bare predicate
/// (no path condition — this is one isolated expression).
pub struct ExprLowering {
    /// The value term.
    pub term: TermId,
    /// The value's scalar type.
    pub ty: Ty,
    /// `(label, predicate)` pairs; each predicate is satisfiable exactly when the
    /// expression hits that panic class.
    pub bad_predicates: Vec<(String, TermId)>,
}

/// Lowers a pure scalar [`Expr`] against `env` (variable name → `(term, ty)`),
/// reusing the same overflow-/signedness-correct lowering as whole-program
/// verification. The loop→`TransitionSystem` builder (C4.3) uses this to lower a
/// loop's guard and per-variable update/assert expressions against a BMC step's
/// pre-state symbols. Arrays are not in scope here (scalar loop fragment only).
///
/// # Errors
///
/// Returns [`LowerError`] for an out-of-fragment expression or an unknown
/// variable.
pub fn lower_pure_expr(
    arena: &mut TermArena,
    env: &[(String, TermId, Ty)],
    e: &Expr,
) -> Result<ExprLowering, LowerError> {
    let mut map = HashMap::new();
    for (name, term, ty) in env {
        map.insert(
            name.clone(),
            SymVal {
                term: *term,
                ty: *ty,
            },
        );
    }
    let mut lowerer = Lowerer {
        arena,
        env: map,
        arrays: HashMap::new(),
        path: Vec::new(),
        bad_states: Vec::new(),
        scopes: Vec::new(),
    };
    let val = lowerer.lower_expr(e)?;
    let bad_predicates = lowerer
        .bad_states
        .into_iter()
        .map(|b| (b.label, b.term))
        .collect();
    Ok(ExprLowering {
        term: val.term,
        ty: val.ty,
        bad_predicates,
    })
}

fn declare_scalar(arena: &mut TermArena, name: &str, ty: Ty) -> Result<SymbolId, LowerError> {
    let sort = match ty {
        Ty::Int { width, .. } => axeyum_ir::Sort::BitVec(width),
        Ty::Bool => axeyum_ir::Sort::Bool,
    };
    arena.declare(name, sort).map_err(|e| ir(&e))
}
