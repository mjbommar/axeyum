//! The ground evaluator: the executable semantic reference.
//!
//! Every other layer (rewriter, bit-blaster, backends) is validated against
//! this evaluator; its semantics follow the SMT-LIB conventions recorded in
//! the bv-semantics research note. All operators are total.

use std::collections::HashMap;

use crate::arena::TermArena;
use crate::error::IrError;
use crate::rational::Rational;
use crate::sort::{Sort, mask};
use crate::term::{DatatypeId, FuncId, Op, SymbolId, TermId, TermNode};
use crate::value::{ArrayValue, FuncValue, Value};

/// A binding of symbols to concrete values (and uninterpreted functions to
/// interpretations), used as evaluator input.
#[derive(Debug, Clone, Default)]
pub struct Assignment {
    bindings: HashMap<SymbolId, Value>,
    functions: HashMap<FuncId, FuncValue>,
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
        self.bindings.get(&symbol).cloned()
    }

    /// Binds uninterpreted function `func` to interpretation `value`, replacing
    /// any previous binding.
    pub fn set_function(&mut self, func: FuncId, value: FuncValue) {
        self.functions.insert(func, value);
    }

    /// The interpretation bound to `func`, if any.
    pub fn function(&self, func: FuncId) -> Option<&FuncValue> {
        self.functions.get(&func)
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

/// The well-founded default value of `sort` — the chosen-total convention for
/// `select` over a wrong constructor (ADR-0022 step-B gate).
///
/// Selecting field `i` of constructor `c` from a value built with a *different*
/// constructor returns this default of field `i`'s sort, so the evaluator stays
/// total and a projected `Value::Datatype` model (from native datatype solving)
/// replays soundly. Any expansion of datatype variables must use this same
/// default.
///
/// Returns `None` only for an *uninhabited* datatype (no well-founded
/// constructor — e.g. `Stream = cons(head, tail: Stream)` with no base case),
/// where no finite value exists. For inhabited sorts the result is `Some`, so
/// `select` is total in practice.
#[must_use]
pub fn well_founded_default(arena: &TermArena, sort: Sort) -> Option<Value> {
    well_founded_default_rec(arena, sort, &mut Vec::new())
}

/// Recursive worker for [`well_founded_default`]; `visiting` tracks the
/// datatypes currently being constructed so a cyclic (non-well-founded) path is
/// abandoned in favour of a base constructor.
fn well_founded_default_rec(
    arena: &TermArena,
    sort: Sort,
    visiting: &mut Vec<DatatypeId>,
) -> Option<Value> {
    match sort {
        Sort::Bool => Some(Value::Bool(false)),
        Sort::BitVec(width) => Some(Value::Bv { width, value: 0 }),
        Sort::Int => Some(Value::Int(0)),
        Sort::Real => Some(Value::Real(Rational::zero())),
        Sort::Array { index, element } => Some(Value::Array(ArrayValue::constant(
            index, element, 0,
        ))),
        Sort::Datatype(dt) => {
            if visiting.contains(&dt) {
                // Recursing back into `dt` mid-construction: this path is not
                // well-founded. Another constructor (a base case) may still be.
                return None;
            }
            visiting.push(dt);
            let mut chosen = None;
            for &ctor in arena.datatype_constructors(dt) {
                let fields = arena.constructor_fields(ctor);
                let mut field_vals = Vec::with_capacity(fields.len());
                let mut ok = true;
                for (_, fsort) in fields {
                    if let Some(v) = well_founded_default_rec(arena, *fsort, visiting) {
                        field_vals.push(v);
                    } else {
                        ok = false;
                        break;
                    }
                }
                if ok {
                    chosen = Some(Value::Datatype {
                        datatype: dt,
                        constructor: ctor,
                        fields: field_vals,
                    });
                    break;
                }
            }
            visiting.pop();
            chosen
        }
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
            TermNode::IntConst(value) => {
                memo.insert(t, Value::Int(*value));
            }
            TermNode::RealConst(value) => {
                memo.insert(t, Value::Real(*value));
            }
            TermNode::Symbol(s) => {
                let v = assignment.get(*s).ok_or(IrError::UnboundSymbol(*s))?;
                memo.insert(t, v);
            }
            TermNode::App { op, args } => match op {
                // Quantifiers bind a symbol and range over its domain, so their
                // body is *not* evaluated in the shared memo: each binding gets a
                // fresh sub-evaluation (ADR-0016).
                Op::Forall(var) | Op::Exists(var) => {
                    let is_forall = matches!(op, Op::Forall(_));
                    let value = eval_quantifier(arena, *var, args[0], is_forall, assignment)?;
                    memo.insert(t, value);
                }
                _ => {
                    if children_ready {
                        let vals: Vec<Value> = args.iter().map(|a| memo[a].clone()).collect();
                        let value = match op {
                            // Uninterpreted functions have no fixed semantics: the
                            // interpretation comes from the model, the result sort
                            // from the function's declaration (carried by the term).
                            Op::Apply(func) => {
                                let interp = assignment
                                    .function(*func)
                                    .ok_or(IrError::UnboundFunction(*func))?;
                                let key: Vec<u128> = vals.iter().map(Value::scalar_code).collect();
                                let code = interp.apply(&key);
                                Value::from_scalar_code(arena.sort_of(t), code)
                            }
                            Op::DtConstruct {
                                constructor,
                                datatype,
                            } => Value::Datatype {
                                datatype: *datatype,
                                constructor: *constructor,
                                fields: vals.clone(),
                            },
                            Op::DtSelect { constructor, index } => match &vals[0] {
                                Value::Datatype {
                                    constructor: built,
                                    fields,
                                    ..
                                } if built == constructor => fields[*index as usize].clone(),
                                Value::Datatype { .. } => {
                                    // Selecting a field of `constructor` from a value built
                                    // with a *different* constructor is the chosen-total
                                    // convention (ADR-0022 step-B gate): return the
                                    // well-founded default of the field's sort, so `select`
                                    // is total and projected datatype models replay soundly.
                                    let field_sort =
                                        arena.constructor_fields(*constructor)[*index as usize].1;
                                    match well_founded_default(arena, field_sort) {
                                        Some(v) => v,
                                        // Only an *uninhabited* field sort has no value.
                                        None => {
                                            return Err(IrError::DatatypeConstructorMismatch);
                                        }
                                    }
                                }
                                _ => unreachable!("builder guaranteed datatype operand"),
                            },
                            Op::DtTest(constructor) => match &vals[0] {
                                Value::Datatype {
                                    constructor: built, ..
                                } => Value::Bool(built == constructor),
                                _ => unreachable!("builder guaranteed datatype operand"),
                            },
                            _ => apply(*op, &vals),
                        };
                        memo.insert(t, value);
                    } else {
                        stack.push((t, true));
                        for &a in &**args {
                            stack.push((a, false));
                        }
                    }
                }
            },
        }
    }

    Ok(memo[&term].clone())
}

/// The largest bit-vector width a quantifier may range over in the evaluator
/// (`2^16` enumerated values); wider domains are an error.
const QUANTIFIER_EVAL_BIT_LIMIT: u32 = 16;

/// Evaluates `forall var. body` (or `exists`) by enumerating every value of
/// `var`'s sort, binding it, and conjoining (`forall`) / disjoining (`exists`)
/// the body's value, short-circuiting on the decisive case.
fn eval_quantifier(
    arena: &TermArena,
    var: SymbolId,
    body: TermId,
    is_forall: bool,
    assignment: &Assignment,
) -> Result<Value, IrError> {
    let sort = arena.symbol(var).1;
    let mut sub = assignment.clone();
    let mut check = |value: Value| -> Result<Option<bool>, IrError> {
        sub.set(var, value);
        let outcome = eval(arena, body, &sub)?
            .as_bool()
            .expect("quantified body is Bool-sorted");
        // Short-circuit: `forall` fails on the first false, `exists` succeeds on
        // the first true — i.e. when `outcome` differs from `is_forall`.
        if outcome ^ is_forall {
            Ok(Some(outcome))
        } else {
            Ok(None)
        }
    };
    match sort {
        Sort::Bool => {
            for value in [Value::Bool(false), Value::Bool(true)] {
                if let Some(decisive) = check(value)? {
                    return Ok(Value::Bool(decisive));
                }
            }
        }
        Sort::BitVec(width) if width <= QUANTIFIER_EVAL_BIT_LIMIT => {
            for value in 0..(1u128 << width) {
                if let Some(decisive) = check(Value::Bv { width, value })? {
                    return Ok(Value::Bool(decisive));
                }
            }
        }
        other => return Err(IrError::UnsupportedQuantifierDomain(other)),
    }
    // No decisive case: `forall` holds, `exists` does not.
    Ok(Value::Bool(is_forall))
}

/// Applies an operator to already-evaluated operand values.
///
/// Operand sorts are guaranteed by the typed builders, so mismatches here
/// are internal invariant violations and panic.
// A flat dispatch over the whole operator enum reads better than an
// artificial split; length is inherent to the operator count.
#[allow(clippy::too_many_lines)]
fn apply(op: Op, vals: &[Value]) -> Value {
    let b = |v: &Value| v.as_bool().expect("builder guaranteed Bool operand");
    let bv = |v: &Value| v.as_bv().expect("builder guaranteed BitVec operand");
    let int = |v: &Value| v.as_int().expect("builder guaranteed Int operand");
    let real = |v: &Value| v.as_real().expect("builder guaranteed Real operand");
    match op {
        // --- Boolean ------------------------------------------------------
        Op::BoolNot => Value::Bool(!b(&vals[0])),
        Op::BoolAnd => Value::Bool(b(&vals[0]) && b(&vals[1])),
        Op::BoolOr => Value::Bool(b(&vals[0]) || b(&vals[1])),
        Op::BoolXor => Value::Bool(b(&vals[0]) ^ b(&vals[1])),
        Op::BoolImplies => Value::Bool(!b(&vals[0]) || b(&vals[1])),
        // --- bitwise -------------------------------------------------------
        Op::BvNot => {
            let (w, v) = bv(&vals[0]);
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
            let (w, v) = bv(&vals[0]);
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
            let (w, x) = bv(&vals[0]);
            let (_, k) = bv(&vals[1]);
            let value = if k >= u128::from(w) {
                0
            } else {
                (x << k) & mask(w)
            };
            Value::Bv { width: w, value }
        }
        Op::BvLshr => {
            let (w, x) = bv(&vals[0]);
            let (_, k) = bv(&vals[1]);
            let value = if k >= u128::from(w) { 0 } else { x >> k };
            Value::Bv { width: w, value }
        }
        Op::BvAshr => {
            let (w, x) = bv(&vals[0]);
            let (_, k) = bv(&vals[1]);
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
            if b(&vals[0]) {
                vals[1].clone()
            } else {
                vals[2].clone()
            }
        }
        // --- structural -----------------------------------------------------------
        Op::BvComp => {
            let (_, x) = bv(&vals[0]);
            let (_, y) = bv(&vals[1]);
            Value::Bv {
                width: 1,
                value: u128::from(x == y),
            }
        }
        Op::Extract { hi, lo } => {
            let (_, v) = bv(&vals[0]);
            let out = hi - lo + 1;
            Value::Bv {
                width: out,
                value: (v >> lo) & mask(out),
            }
        }
        Op::Concat => {
            let (wa, a) = bv(&vals[0]);
            let (wb, bb) = bv(&vals[1]);
            Value::Bv {
                width: wa + wb,
                value: ((a << wb) | bb) & mask(wa + wb),
            }
        }
        Op::ZeroExt { by } => {
            let (w, v) = bv(&vals[0]);
            Value::Bv {
                width: w + by,
                value: v,
            }
        }
        Op::SignExt { by } => {
            let (w, v) = bv(&vals[0]);
            let out = w + by;
            let sign = (v >> (w - 1)) & 1 == 1;
            let value = if sign { v | (mask(out) ^ mask(w)) } else { v };
            Value::Bv { width: out, value }
        }
        Op::RotateLeft { by } => rotate(&vals[0], by, true),
        Op::RotateRight { by } => rotate(&vals[0], by, false),
        // --- arrays (ADR-0010) ---------------------------------------------------
        Op::Select => {
            let array = vals[0]
                .as_array()
                .expect("builder guaranteed Array operand");
            let (_, index) = bv(&vals[1]);
            Value::Bv {
                width: array.element_width(),
                value: array.select(index),
            }
        }
        Op::Store => {
            let array = vals[0]
                .as_array()
                .expect("builder guaranteed Array operand");
            let (_, index) = bv(&vals[1]);
            let (_, element) = bv(&vals[2]);
            Value::Array(array.store(index, element))
        }
        Op::ConstArray { index } => {
            let (element_width, value) = bv(&vals[0]);
            Value::Array(ArrayValue::constant(index, element_width, value))
        }
        Op::IntToReal => {
            let i = vals[0].as_int().expect("builder guaranteed Int operand");
            Value::Real(crate::rational::Rational::integer(i))
        }
        Op::RealToInt => {
            let r = real(&vals[0]);
            // Floor: denominator is positive by normalization.
            Value::Int(r.numerator().div_euclid(r.denominator()))
        }
        Op::RealIsInt => {
            let r = real(&vals[0]);
            Value::Bool(r.denominator() == 1)
        }
        Op::Bv2Nat => {
            let (_, value) = bv(&vals[0]);
            // Unsigned BV value as a non-negative integer (within the i128
            // reference range; widths up to 127 are exact).
            #[allow(clippy::cast_possible_wrap)]
            Value::Int(value as i128)
        }
        Op::Int2Bv { width } => {
            let x = vals[0].as_int().expect("builder guaranteed Int operand");
            // x mod 2^width: the low `width` bits of x's two's-complement form.
            #[allow(clippy::cast_sign_loss)]
            let value = (x as u128) & mask(width);
            Value::Bv { width, value }
        }
        // Handled in `eval` (needs the model interpretation and result sort).
        Op::Apply(_) => unreachable!("Op::Apply is evaluated against the model in `eval`"),
        // --- linear integer arithmetic (ADR-0014) --------------------------------
        // Integers are exact within the i128 reference range; out-of-range
        // intermediate values are a usage error (the bounded-LIA contract).
        Op::IntNeg => {
            let x = int(&vals[0]);
            Value::Int(x.checked_neg().expect("integer negation within i128 range"))
        }
        Op::IntAdd => int_bin(vals, "addition", i128::checked_add),
        Op::IntSub => int_bin(vals, "subtraction", i128::checked_sub),
        Op::IntMul => int_bin(vals, "multiplication", i128::checked_mul),
        // Euclidean div/mod (SMT-LIB): `mod` always in `0..|b|`; by convention
        // `div a 0 = 0` and `mod a 0 = a`. `div_euclid`/`rem_euclid` implement
        // exactly the Euclidean semantics for `b ≠ 0`.
        Op::IntDiv => {
            let x = vals[0].as_int().expect("builder guaranteed Int operand");
            let y = vals[1].as_int().expect("builder guaranteed Int operand");
            let q = if y == 0 {
                0
            } else {
                x.checked_div_euclid(y).expect("integer division within i128 range")
            };
            Value::Int(q)
        }
        Op::IntMod => {
            let x = vals[0].as_int().expect("builder guaranteed Int operand");
            let y = vals[1].as_int().expect("builder guaranteed Int operand");
            let r = if y == 0 { x } else { x.rem_euclid(y) };
            Value::Int(r)
        }
        Op::IntAbs => {
            let x = vals[0].as_int().expect("builder guaranteed Int operand");
            Value::Int(x.checked_abs().expect("integer abs within i128 range"))
        }
        Op::IntLt => int_cmp(vals, |x, y| x < y),
        Op::IntLe => int_cmp(vals, |x, y| x <= y),
        Op::IntGt => int_cmp(vals, |x, y| x > y),
        Op::IntGe => int_cmp(vals, |x, y| x >= y),
        // --- linear real arithmetic (ADR-0015) -----------------------------------
        // Exact rational arithmetic; overflow within `Rational` is a usage error.
        Op::RealNeg => Value::Real(-real(&vals[0])),
        Op::RealAdd => Value::Real(real(&vals[0]) + real(&vals[1])),
        Op::RealSub => Value::Real(real(&vals[0]) - real(&vals[1])),
        Op::RealMul => Value::Real(real(&vals[0]) * real(&vals[1])),
        Op::RealDiv => {
            let (a, b) = (real(&vals[0]), real(&vals[1]));
            // Convention: x / 0 = 0 (SMT-LIB leaves it unspecified).
            if b == crate::rational::Rational::integer(0) {
                Value::Real(crate::rational::Rational::integer(0))
            } else {
                Value::Real(a / b)
            }
        }
        Op::RealLt => Value::Bool(real(&vals[0]) < real(&vals[1])),
        Op::RealLe => Value::Bool(real(&vals[0]) <= real(&vals[1])),
        Op::RealGt => Value::Bool(real(&vals[0]) > real(&vals[1])),
        Op::RealGe => Value::Bool(real(&vals[0]) >= real(&vals[1])),
        // Handled in `eval` (they bind a variable and enumerate its domain).
        Op::Forall(_) | Op::Exists(_) => {
            unreachable!("quantifiers are evaluated by enumeration in `eval`")
        }
        // Handled in `eval` (datatype ops need arena + `Result`).
        Op::DtConstruct { .. } | Op::DtSelect { .. } | Op::DtTest(_) => {
            unreachable!("datatype ops are evaluated in `eval`")
        }
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

fn int_bin(vals: &[Value], what: &str, f: impl Fn(i128, i128) -> Option<i128>) -> Value {
    let x = vals[0].as_int().expect("builder guaranteed Int operand");
    let y = vals[1].as_int().expect("builder guaranteed Int operand");
    Value::Int(f(x, y).unwrap_or_else(|| panic!("integer {what} within i128 range")))
}

fn int_cmp(vals: &[Value], f: impl Fn(i128, i128) -> bool) -> Value {
    let x = vals[0].as_int().expect("builder guaranteed Int operand");
    let y = vals[1].as_int().expect("builder guaranteed Int operand");
    Value::Bool(f(x, y))
}

fn rotate(val: &Value, by: u32, left: bool) -> Value {
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
