//! The ground evaluator: the executable semantic reference.
//!
//! Every other layer (rewriter, bit-blaster, backends) is validated against
//! this evaluator; its semantics follow the SMT-LIB conventions recorded in
//! the bv-semantics research note. All operators are total.

use std::collections::HashMap;

use crate::arena::TermArena;
use crate::error::IrError;
use crate::sort::mask;
use crate::term::{Op, SymbolId, TermId, TermNode};
use crate::value::Value;

/// A binding of symbols to concrete values, used as evaluator input.
#[derive(Debug, Clone, Default)]
pub struct Assignment {
    bindings: HashMap<SymbolId, Value>,
}

impl Assignment {
    /// Creates an empty assignment.
    pub fn new() -> Self {
        Self::default()
    }

    /// Binds `symbol` to `value`, replacing any previous binding.
    pub fn set(&mut self, symbol: SymbolId, value: Value) {
        self.bindings.insert(symbol, value);
    }

    /// The value bound to `symbol`, if any.
    pub fn get(&self, symbol: SymbolId) -> Option<Value> {
        self.bindings.get(&symbol).copied()
    }

    /// Number of bound symbols.
    pub fn len(&self) -> usize {
        self.bindings.len()
    }

    /// Returns `true` if no symbols are bound.
    pub fn is_empty(&self) -> bool {
        self.bindings.is_empty()
    }
}

/// Evaluates `term` under `assignment`.
///
/// # Errors
///
/// Returns [`IrError::UnboundSymbol`] if the term references a symbol the
/// assignment does not bind. Sort errors cannot occur on terms built through
/// the typed builders.
///
/// # Panics
///
/// Panics if `term` does not belong to `arena`, or on arena corruption
/// (internal invariant violations).
pub fn eval(arena: &TermArena, term: TermId, assignment: &Assignment) -> Result<Value, IrError> {
    // Iterative post-order evaluation with memoization, so deep terms cannot
    // overflow the call stack and shared subterms evaluate once.
    let mut memo: HashMap<TermId, Value> = HashMap::new();
    let mut stack: Vec<(TermId, bool)> = vec![(term, false)];

    while let Some((t, children_ready)) = stack.pop() {
        if memo.contains_key(&t) {
            continue;
        }
        match arena.node(t) {
            TermNode::BoolConst(b) => {
                memo.insert(t, Value::Bool(*b));
            }
            TermNode::BvConst { width, value } => {
                memo.insert(
                    t,
                    Value::Bv {
                        width: *width,
                        value: *value,
                    },
                );
            }
            TermNode::Symbol(s) => {
                let v = assignment.get(*s).ok_or(IrError::UnboundSymbol(*s))?;
                memo.insert(t, v);
            }
            TermNode::App { op, args } => {
                if children_ready {
                    let vals: Vec<Value> = args.iter().map(|a| memo[a]).collect();
                    memo.insert(t, apply(*op, &vals));
                } else {
                    stack.push((t, true));
                    for &a in &**args {
                        stack.push((a, false));
                    }
                }
            }
        }
    }

    Ok(memo[&term])
}

/// Applies an operator to already-evaluated operand values.
///
/// Operand sorts are guaranteed by the typed builders, so mismatches here
/// are internal invariant violations and panic.
// A flat dispatch over the whole operator enum reads better than an
// artificial split; length is inherent to the operator count.
#[allow(clippy::too_many_lines)]
fn apply(op: Op, vals: &[Value]) -> Value {
    let b = |v: Value| v.as_bool().expect("builder guaranteed Bool operand");
    let bv = |v: Value| v.as_bv().expect("builder guaranteed BitVec operand");
    match op {
        // --- Boolean ------------------------------------------------------
        Op::BoolNot => Value::Bool(!b(vals[0])),
        Op::BoolAnd => Value::Bool(b(vals[0]) && b(vals[1])),
        Op::BoolOr => Value::Bool(b(vals[0]) || b(vals[1])),
        Op::BoolXor => Value::Bool(b(vals[0]) ^ b(vals[1])),
        Op::BoolImplies => Value::Bool(!b(vals[0]) || b(vals[1])),
        // --- bitwise -------------------------------------------------------
        Op::BvNot => {
            let (w, v) = bv(vals[0]);
            Value::Bv {
                width: w,
                value: !v & mask(w),
            }
        }
        Op::BvAnd => bin_bv(vals, |x, y| x & y),
        Op::BvOr => bin_bv(vals, |x, y| x | y),
        Op::BvXor => bin_bv(vals, |x, y| x ^ y),
        Op::BvNand => bin_bv(vals, |x, y| !(x & y)),
        Op::BvNor => bin_bv(vals, |x, y| !(x | y)),
        Op::BvXnor => bin_bv(vals, |x, y| !(x ^ y)),
        // --- arithmetic ------------------------------------------------------
        Op::BvNeg => {
            let (w, v) = bv(vals[0]);
            Value::Bv {
                width: w,
                value: v.wrapping_neg() & mask(w),
            }
        }
        Op::BvAdd => bin_bv(vals, u128::wrapping_add),
        Op::BvSub => bin_bv(vals, u128::wrapping_sub),
        Op::BvMul => bin_bv(vals, u128::wrapping_mul),
        Op::BvUdiv => bin_bv(vals, |x, y| x.checked_div(y).unwrap_or(u128::MAX)),
        Op::BvUrem => bin_bv(vals, |x, y| x.checked_rem(y).unwrap_or(x)),
        Op::BvSdiv => signed_bin(vals, |x, y| {
            if y == 0 {
                // SMT-LIB expansion: -1 for non-negative dividend, +1 else.
                if x >= 0 { -1 } else { 1 }
            } else {
                // Truncating division; i128::MIN / -1 wraps (width 128).
                x.checked_div(y).unwrap_or(x)
            }
        }),
        Op::BvSrem => signed_bin(vals, |x, y| {
            if y == 0 {
                x
            } else {
                // Sign follows the dividend; i128::MIN % -1 is 0.
                x.checked_rem(y).unwrap_or(0)
            }
        }),
        Op::BvSmod => signed_bin(vals, |x, y| {
            if y == 0 {
                x
            } else {
                let r = x.checked_rem(y).unwrap_or(0);
                // Sign follows the divisor (SMT-LIB bvsmod expansion).
                if r == 0 || (r < 0) == (y < 0) {
                    r
                } else {
                    r + y
                }
            }
        }),
        // --- shifts ----------------------------------------------------------
        Op::BvShl => {
            let (w, x) = bv(vals[0]);
            let (_, k) = bv(vals[1]);
            let value = if k >= u128::from(w) {
                0
            } else {
                (x << k) & mask(w)
            };
            Value::Bv { width: w, value }
        }
        Op::BvLshr => {
            let (w, x) = bv(vals[0]);
            let (_, k) = bv(vals[1]);
            let value = if k >= u128::from(w) { 0 } else { x >> k };
            Value::Bv { width: w, value }
        }
        Op::BvAshr => {
            let (w, x) = bv(vals[0]);
            let (_, k) = bv(vals[1]);
            let sign = (x >> (w - 1)) & 1 == 1;
            let value = if k >= u128::from(w) {
                if sign { mask(w) } else { 0 }
            } else {
                // i128 shift-right is arithmetic; k < w <= 128 here.
                #[allow(clippy::cast_possible_truncation)]
                let shift = k as u32;
                from_signed(w, to_signed(w, x) >> shift)
            };
            Value::Bv { width: w, value }
        }
        // --- comparisons -------------------------------------------------------
        Op::BvUlt => cmp_bv(vals, |x, y| x < y),
        Op::BvUle => cmp_bv(vals, |x, y| x <= y),
        Op::BvUgt => cmp_bv(vals, |x, y| x > y),
        Op::BvUge => cmp_bv(vals, |x, y| x >= y),
        Op::BvSlt => cmp_signed(vals, |x, y| x < y),
        Op::BvSle => cmp_signed(vals, |x, y| x <= y),
        Op::BvSgt => cmp_signed(vals, |x, y| x > y),
        Op::BvSge => cmp_signed(vals, |x, y| x >= y),
        // --- polymorphic ---------------------------------------------------------
        Op::Eq => Value::Bool(vals[0] == vals[1]),
        Op::Ite => {
            if b(vals[0]) {
                vals[1]
            } else {
                vals[2]
            }
        }
        // --- structural -----------------------------------------------------------
        Op::BvComp => {
            let (_, x) = bv(vals[0]);
            let (_, y) = bv(vals[1]);
            Value::Bv {
                width: 1,
                value: u128::from(x == y),
            }
        }
        Op::Extract { hi, lo } => {
            let (_, v) = bv(vals[0]);
            let out = hi - lo + 1;
            Value::Bv {
                width: out,
                value: (v >> lo) & mask(out),
            }
        }
        Op::Concat => {
            let (wa, a) = bv(vals[0]);
            let (wb, bb) = bv(vals[1]);
            Value::Bv {
                width: wa + wb,
                value: ((a << wb) | bb) & mask(wa + wb),
            }
        }
        Op::ZeroExt { by } => {
            let (w, v) = bv(vals[0]);
            Value::Bv {
                width: w + by,
                value: v,
            }
        }
        Op::SignExt { by } => {
            let (w, v) = bv(vals[0]);
            let out = w + by;
            let sign = (v >> (w - 1)) & 1 == 1;
            let value = if sign { v | (mask(out) ^ mask(w)) } else { v };
            Value::Bv { width: out, value }
        }
        Op::RotateLeft { by } => rotate(vals[0], by, true),
        Op::RotateRight { by } => rotate(vals[0], by, false),
    }
}

/// Interprets a masked value as a two's-complement signed integer.
fn to_signed(width: u32, value: u128) -> i128 {
    let sign = (value >> (width - 1)) & 1 == 1;
    let extended = if sign { value | !mask(width) } else { value };
    #[allow(clippy::cast_possible_wrap)]
    let signed = extended as i128;
    signed
}

/// Masks a signed result back into `width` bits.
fn from_signed(width: u32, value: i128) -> u128 {
    #[allow(clippy::cast_sign_loss)]
    let unsigned = value as u128;
    unsigned & mask(width)
}

fn bin_bv(vals: &[Value], f: impl Fn(u128, u128) -> u128) -> Value {
    let (w, x) = vals[0].as_bv().expect("builder guaranteed BitVec operand");
    let (_, y) = vals[1].as_bv().expect("builder guaranteed BitVec operand");
    Value::Bv {
        width: w,
        value: f(x, y) & mask(w),
    }
}

fn signed_bin(vals: &[Value], f: impl Fn(i128, i128) -> i128) -> Value {
    let (w, x) = vals[0].as_bv().expect("builder guaranteed BitVec operand");
    let (_, y) = vals[1].as_bv().expect("builder guaranteed BitVec operand");
    Value::Bv {
        width: w,
        value: from_signed(w, f(to_signed(w, x), to_signed(w, y))),
    }
}

fn cmp_bv(vals: &[Value], f: impl Fn(u128, u128) -> bool) -> Value {
    let (_, x) = vals[0].as_bv().expect("builder guaranteed BitVec operand");
    let (_, y) = vals[1].as_bv().expect("builder guaranteed BitVec operand");
    Value::Bool(f(x, y))
}

fn cmp_signed(vals: &[Value], f: impl Fn(i128, i128) -> bool) -> Value {
    let (w, x) = vals[0].as_bv().expect("builder guaranteed BitVec operand");
    let (_, y) = vals[1].as_bv().expect("builder guaranteed BitVec operand");
    Value::Bool(f(to_signed(w, x), to_signed(w, y)))
}

fn rotate(val: Value, by: u32, left: bool) -> Value {
    let (w, v) = val.as_bv().expect("builder guaranteed BitVec operand");
    // Builders normalize `by` modulo width, so 0 <= by < w here.
    let k = if left { by } else { (w - by) % w };
    let value = if k == 0 {
        v
    } else {
        ((v << k) | (v >> (w - k))) & mask(w)
    };
    Value::Bv { width: w, value }
}
