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
fn apply(op: Op, vals: &[Value]) -> Value {
    let b = |v: Value| v.as_bool().expect("builder guaranteed Bool operand");
    let bv = |v: Value| v.as_bv().expect("builder guaranteed BitVec operand");
    match op {
        Op::BoolNot => Value::Bool(!b(vals[0])),
        Op::BoolAnd => Value::Bool(b(vals[0]) && b(vals[1])),
        Op::BoolOr => Value::Bool(b(vals[0]) || b(vals[1])),
        Op::BoolXor => Value::Bool(b(vals[0]) ^ b(vals[1])),
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
        Op::BvAdd => bin_bv(vals, u128::wrapping_add),
        Op::BvUlt => {
            let (_, x) = bv(vals[0]);
            let (_, y) = bv(vals[1]);
            Value::Bool(x < y)
        }
        Op::Eq => Value::Bool(vals[0] == vals[1]),
        Op::Ite => {
            if b(vals[0]) {
                vals[1]
            } else {
                vals[2]
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
    }
}

fn bin_bv(vals: &[Value], f: impl Fn(u128, u128) -> u128) -> Value {
    let (w, x) = vals[0].as_bv().expect("builder guaranteed BitVec operand");
    let (_, y) = vals[1].as_bv().expect("builder guaranteed BitVec operand");
    Value::Bv {
        width: w,
        value: f(x, y) & mask(w),
    }
}
