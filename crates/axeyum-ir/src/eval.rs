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
        // A floating-point default is +0.0: the all-zero `exp + sig`-bit pattern.
        Sort::Float { exp, sig } => Some(Value::Bv {
            width: exp + sig,
            value: 0,
        }),
        Sort::Int => Some(Value::Int(0)),
        Sort::Real => Some(Value::Real(Rational::zero())),
        Sort::Array { index, element } => {
            Some(Value::Array(ArrayValue::constant(index, element, 0)))
        }
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
    let mut memo: HashMap<TermId, Value> = HashMap::new();
    eval_with_memo(arena, term, assignment, &mut memo)
}

/// Like [`eval`], but evaluates against a caller-supplied `memo` of already-known
/// subterm values, leaving every newly-computed subterm value in it.
///
/// This is the primitive for **incremental** re-evaluation: a caller that keeps a
/// persistent `memo` across many assignments — invalidating (removing) only the
/// subterms whose value depends on a changed symbol — recomputes just those nodes,
/// reusing every unchanged subterm from `memo`. The values left in `memo` are valid
/// only for `assignment`; **the caller owns invalidation** when the assignment
/// changes (a stale entry is silently trusted). With an empty `memo` this is exactly
/// [`eval`].
///
/// # Errors
///
/// Same as [`eval`] ([`IrError::UnboundSymbol`] for an unbound symbol).
///
/// # Panics
///
/// Same as [`eval`].
#[allow(clippy::implicit_hasher)] // callers pass the default-hasher `HashMap<TermId, Value>`.
pub fn eval_with_memo(
    arena: &TermArena,
    term: TermId,
    assignment: &Assignment,
    memo: &mut HashMap<TermId, Value>,
) -> Result<Value, IrError> {
    // Iterative post-order evaluation with memoization, so deep terms cannot
    // overflow the call stack and shared subterms evaluate once.
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
            TermNode::WideBvConst(w) => {
                memo.insert(t, Value::WideBv(w.clone()));
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
                                // `apply_value` handles both storage modes: scalar
                                // (`Bool`/`BitVec`/`Float`) functions code their
                                // keys to `u128` internally, while arithmetic
                                // (`Int`/`Real`) functions compare full `Value`
                                // keys — so `QF_UFLIA`/`QF_UFLRA` interpretations
                                // replay through the same path.
                                interp.apply_value(&vals)
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
                            _ => apply(*op, &vals)?,
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
        // A floating-point domain enumerates its `exp + sig`-bit patterns; an FP
        // value is represented as that bit-vector (ADR-0026).
        Sort::Float { exp, sig } if exp + sig <= QUANTIFIER_EVAL_BIT_LIMIT => {
            let width = exp + sig;
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
/// are internal invariant violations and panic. By contrast, arithmetic
/// *overflow* (an `i128`-range result for Int/Real/bv2nat) is user-triggerable,
/// not an invariant violation, so it is reported as
/// [`IrError::ArithmeticOverflow`] (never a panic, never a wrapped wrong value):
/// the evaluator is the soundness trust anchor.
// A flat dispatch over the whole operator enum reads better than an
// artificial split; length is inherent to the operator count.
#[allow(clippy::too_many_lines)]
fn apply(op: Op, vals: &[Value]) -> Result<Value, IrError> {
    // `bv2nat` of a WIDE (> 128-bit) operand crosses BV → Int, so it does NOT
    // belong on the "infallible, pure mod-2^width" wide path below (which has no
    // `Bv2Nat` arm and would panic). A wide value is non-negative; it has a
    // non-negative `i128` representation iff no bit at index ≥ 127 is set (i.e. it
    // is < 2^127 = i128::MAX + 1). Otherwise report overflow — never crash, never
    // wrap to a wrong (negative) integer.
    if matches!(op, Op::Bv2Nat) {
        if let Some(Value::WideBv(w)) = vals.first() {
            if (127..w.width()).any(|i| w.bit(i)) {
                return Err(IrError::ArithmeticOverflow { op: "bv2nat" });
            }
            // No bit at index ≥ 127 is set, so the value is < 2^127 ≤ i128::MAX:
            // reconstruct it from its low bits (`to_u128` is unavailable for
            // width > 128). Each set bit contributes `2^i` with `i < 127`.
            let mut value: u128 = 0;
            for i in 0..127 {
                if w.bit(i) {
                    value |= 1u128 << i;
                }
            }
            #[allow(clippy::cast_possible_wrap)] // guarded: value < 2^127 ≤ i128::MAX.
            return Ok(Value::Int(value as i128));
        }
    }
    // Bit-vectors wider than 128 bits take a separate path; the `u128` fast path
    // below is unchanged for the common case. This triggers when an operand is
    // already wide, or when a width-*growing* op produces a `> 128`-bit result
    // from `≤ 128`-bit operands (zero/sign-extend, concat, int2bv).
    if vals.iter().any(|v| matches!(v, Value::WideBv(_))) || result_exceeds_128(op, vals) {
        // The wide path is all mod-2^width bit-vector arithmetic (no Int/Real
        // crossing), so it is infallible: no overflow can occur there.
        return Ok(apply_wide(op, vals));
    }
    let b = |v: &Value| v.as_bool().expect("builder guaranteed Bool operand");
    let bv = |v: &Value| v.as_bv().expect("builder guaranteed BitVec operand");
    let int = |v: &Value| v.as_int().expect("builder guaranteed Int operand");
    let real = |v: &Value| v.as_real().expect("builder guaranteed Real operand");
    Ok(match op {
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
        // Real-sorted equality may involve an *algebraic* operand, which is not
        // comparable by the derived structural `==` against a rational (and two
        // algebraic numbers need root-aware equality). Route any pair with a real
        // operand through the exact `real_cmp` (which handles
        // rational/algebraic/mixed); everything else uses structural equality.
        Op::Eq if is_real_value(&vals[0]) || is_real_value(&vals[1]) => {
            Value::Bool(real_cmp(&vals[0], &vals[1])?.is_eq())
        }
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
            // reference range; widths up to 127 are exact). A `u128` with the
            // high bit set is `> i128::MAX` and has no non-negative `i128`
            // representation: report overflow rather than wrapping to a (wrong)
            // negative integer — bv2nat is always non-negative.
            if value > i128::MAX as u128 {
                return Err(IrError::ArithmeticOverflow { op: "bv2nat" });
            }
            #[allow(clippy::cast_possible_wrap)] // guarded: value <= i128::MAX.
            Value::Int(value as i128)
        }
        Op::Int2Bv { width } => {
            let x = vals[0].as_int().expect("builder guaranteed Int operand");
            // x mod 2^width: the low `width` bits of x's two's-complement form.
            #[allow(clippy::cast_sign_loss)]
            let value = (x as u128) & mask(width);
            Value::Bv { width, value }
        }
        // A pure bit reinterpret: the floating-point value is the operand's bits.
        Op::FpFromBits { exp, sig } => {
            let (_, value) = bv(&vals[0]);
            Value::Bv {
                width: exp + sig,
                value,
            }
        }
        // Handled in `eval` (needs the model interpretation and result sort).
        Op::Apply(_) => unreachable!("Op::Apply is evaluated against the model in `eval`"),
        // --- linear integer arithmetic (ADR-0014) --------------------------------
        // Integers are exact within the i128 reference range; out-of-range
        // intermediate values are a usage error (the bounded-LIA contract).
        Op::IntNeg => {
            let x = int(&vals[0]);
            // abs(i128::MIN) has no i128 representation: overflow, not a panic.
            Value::Int(
                x.checked_neg()
                    .ok_or(IrError::ArithmeticOverflow { op: "int_neg" })?,
            )
        }
        Op::IntAdd => int_bin(vals, "int_add", i128::checked_add)?,
        Op::IntSub => int_bin(vals, "int_sub", i128::checked_sub)?,
        Op::IntMul => int_bin(vals, "int_mul", i128::checked_mul)?,
        // Euclidean div/mod (SMT-LIB): `mod` always in `0..|b|`; by convention
        // `div a 0 = 0` and `mod a 0 = a`. `div_euclid`/`rem_euclid` implement
        // exactly the Euclidean semantics for `b ≠ 0`.
        Op::IntDiv => {
            let x = vals[0].as_int().expect("builder guaranteed Int operand");
            let y = vals[1].as_int().expect("builder guaranteed Int operand");
            let q = if y == 0 {
                0
            } else {
                // i128::MIN / -1 overflows: report it rather than panic.
                x.checked_div_euclid(y)
                    .ok_or(IrError::ArithmeticOverflow { op: "int_div" })?
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
            // abs(i128::MIN) has no i128 representation: overflow, not a panic.
            Value::Int(
                x.checked_abs()
                    .ok_or(IrError::ArithmeticOverflow { op: "int_abs" })?,
            )
        }
        Op::IntLt => int_cmp(vals, |x, y| x < y),
        Op::IntLe => int_cmp(vals, |x, y| x <= y),
        Op::IntGt => int_cmp(vals, |x, y| x > y),
        Op::IntGe => int_cmp(vals, |x, y| x >= y),
        // --- linear real arithmetic (ADR-0015) -----------------------------------
        // Exact rational arithmetic. An `i128`-range overflow inside `Rational`
        // (a huge numerator/denominator, or `abs(i128::MIN)`) is reported as
        // `ArithmeticOverflow` rather than panicking — the evaluator never crashes.
        // Real field arithmetic over an *algebraic* operand is deferred past
        // ADR-0038 slice 1: decline exactly (graceful error → caller's `unknown`)
        // rather than return a wrong value. The rational fast path is unchanged.
        Op::RealNeg => {
            if matches!(&vals[0], Value::RealAlgebraic(_)) {
                algebraic_neg(&vals[0])?
            } else {
                Value::Real(
                    real(&vals[0])
                        .checked_neg()
                        .ok_or(IrError::ArithmeticOverflow { op: "real_neg" })?,
                )
            }
        }
        Op::RealAdd => {
            if has_algebraic(vals) {
                algebraic_add(&vals[0], &vals[1], "real_add")?
            } else {
                Value::Real(
                    real(&vals[0])
                        .checked_add(real(&vals[1]))
                        .ok_or(IrError::ArithmeticOverflow { op: "real_add" })?,
                )
            }
        }
        Op::RealSub => {
            if has_algebraic(vals) {
                // a − b = a + (−b).
                let neg_b = algebraic_neg(&vals[1])?;
                algebraic_add(&vals[0], &neg_b, "real_sub")?
            } else {
                Value::Real(
                    real(&vals[0])
                        .checked_sub(real(&vals[1]))
                        .ok_or(IrError::ArithmeticOverflow { op: "real_sub" })?,
                )
            }
        }
        Op::RealMul => {
            if has_algebraic(vals) {
                algebraic_mul(&vals[0], &vals[1], "real_mul")?
            } else {
                Value::Real(
                    real(&vals[0])
                        .checked_mul(real(&vals[1]))
                        .ok_or(IrError::ArithmeticOverflow { op: "real_mul" })?,
                )
            }
        }
        Op::RealDiv => {
            reject_algebraic(vals, "real_div")?;
            let (a, b) = (real(&vals[0]), real(&vals[1]));
            // Convention: x / 0 = 0 (SMT-LIB leaves it unspecified).
            if b == crate::rational::Rational::integer(0) {
                Value::Real(crate::rational::Rational::integer(0))
            } else {
                Value::Real(
                    a.checked_div(b)
                        .ok_or(IrError::ArithmeticOverflow { op: "real_div" })?,
                )
            }
        }
        Op::RealLt => Value::Bool(real_cmp(&vals[0], &vals[1])?.is_lt()),
        Op::RealLe => Value::Bool(real_cmp(&vals[0], &vals[1])?.is_le()),
        Op::RealGt => Value::Bool(real_cmp(&vals[0], &vals[1])?.is_gt()),
        Op::RealGe => Value::Bool(real_cmp(&vals[0], &vals[1])?.is_ge()),
        // Handled in `eval` (they bind a variable and enumerate its domain).
        Op::Forall(_) | Op::Exists(_) => {
            unreachable!("quantifiers are evaluated by enumeration in `eval`")
        }
        // Handled in `eval` (datatype ops need arena + `Result`).
        Op::DtConstruct { .. } | Op::DtSelect { .. } | Op::DtTest(_) => {
            unreachable!("datatype ops are evaluated in `eval`")
        }
    })
}

/// Whether `v` is a real-sorted value (rational or algebraic).
fn is_real_value(v: &Value) -> bool {
    matches!(v, Value::Real(_) | Value::RealAlgebraic(_))
}

/// If any operand is a [`Value::RealAlgebraic`], decline real *field arithmetic*
/// exactly. Used for the operations not yet covered by algebraic field
/// arithmetic (e.g. `RealDiv`).
fn reject_algebraic(vals: &[Value], op: &'static str) -> Result<(), IrError> {
    if vals.iter().any(|v| matches!(v, Value::RealAlgebraic(_))) {
        return Err(IrError::AlgebraicArithmeticUnsupported { op });
    }
    Ok(())
}

/// Whether any operand is a [`Value::RealAlgebraic`] (so the op needs algebraic
/// field arithmetic rather than the rational fast path).
fn has_algebraic(vals: &[Value]) -> bool {
    vals.iter().any(|v| matches!(v, Value::RealAlgebraic(_)))
}

/// Coerce a real-sorted operand into a [`RealAlgebraic`] (lifting a rational `c`
/// to the degree-1 algebraic number with defining poly `q·x − p`). `None` on
/// overflow.
fn as_algebraic(v: &Value) -> Option<crate::real_algebraic::RealAlgebraic> {
    match v {
        Value::RealAlgebraic(a) => Some(a.clone()),
        Value::Real(c) => crate::real_algebraic::RealAlgebraic::from_rational(*c),
        _ => None,
    }
}

/// Map an algebraic result back to a [`Value`]: if its defining polynomial is
/// degree 1 (`q·x − p`), the value is the exact rational `p/q` — return
/// [`Value::Real`] so the model stays rational; otherwise [`Value::RealAlgebraic`].
fn algebraic_to_value(a: crate::real_algebraic::RealAlgebraic) -> Value {
    // A degree-1 (constant-term) defining poly `q·x + r` denotes the exact rational
    // `−r/q`. Only attempt the rational collapse when the poly fits `i128` (it does
    // for any genuinely degree-1 case); a non-`i128`-fitting poly is necessarily
    // higher-degree and stays algebraic.
    if let Some(poly) = a.defining_poly_i128() {
        // Trimmed degree.
        let mut deg = poly.len();
        while deg > 0 && poly[deg - 1] == 0 {
            deg -= 1;
        }
        if deg == 2 {
            // q·x + r with q ≠ 0 ⇒ rational root −r/q.
            let r = poly[0];
            let q = poly[1];
            if let Some(c) = crate::rational::Rational::checked_new(-r, q) {
                return Value::Real(c);
            }
        }
    }
    Value::RealAlgebraic(a)
}

/// `−α` for an algebraic (or lifted-rational) operand, as a [`Value`]. Declines
/// to the graceful algebraic error on overflow / non-isolation.
fn algebraic_neg(v: &Value) -> Result<Value, IrError> {
    let a = as_algebraic(v).ok_or(IrError::AlgebraicArithmeticUnsupported { op: "real_neg" })?;
    let r = a
        .neg()
        .ok_or(IrError::AlgebraicArithmeticUnsupported { op: "real_neg" })?;
    Ok(algebraic_to_value(r))
}

/// `α + β` for real operands at least one of which is algebraic, as a [`Value`].
fn algebraic_add(lhs: &Value, rhs: &Value, op: &'static str) -> Result<Value, IrError> {
    let alpha = as_algebraic(lhs).ok_or(IrError::AlgebraicArithmeticUnsupported { op })?;
    let beta = as_algebraic(rhs).ok_or(IrError::AlgebraicArithmeticUnsupported { op })?;
    let sum = alpha
        .add(&beta)
        .ok_or(IrError::AlgebraicArithmeticUnsupported { op })?;
    Ok(algebraic_to_value(sum))
}

/// `α · β` for real operands at least one of which is algebraic, as a [`Value`].
/// A rational-`0` operand short-circuits to the exact rational `0` (a
/// [`RealAlgebraic`] is never `0`, so only a lifted rational can be zero).
fn algebraic_mul(lhs: &Value, rhs: &Value, op: &'static str) -> Result<Value, IrError> {
    if matches!(lhs, Value::Real(c) if c.is_zero()) || matches!(rhs, Value::Real(c) if c.is_zero())
    {
        return Ok(Value::Real(crate::rational::Rational::zero()));
    }
    let alpha = as_algebraic(lhs).ok_or(IrError::AlgebraicArithmeticUnsupported { op })?;
    let beta = as_algebraic(rhs).ok_or(IrError::AlgebraicArithmeticUnsupported { op })?;
    let prod = alpha
        .mul(&beta)
        .ok_or(IrError::AlgebraicArithmeticUnsupported { op })?;
    Ok(algebraic_to_value(prod))
}

/// Compares two real-sorted operands exactly, supporting *algebraic* operands
/// (ADR-0038): rational vs rational uses cross-multiplication; an algebraic
/// number vs a rational refines its isolating interval ([`crate::RealAlgebraic::compare_rational`]);
/// two algebraic numbers compare equal via root-aware [`PartialEq`] and otherwise
/// by refining both isolating intervals until disjoint.
///
/// Reports [`IrError::ArithmeticOverflow`] (`op: "real_cmp"`) on any `i128`
/// overflow or a refinement that does not converge — never a panic, never a wrong
/// order. The evaluator is the soundness trust anchor.
fn real_cmp(a: &Value, b: &Value) -> Result<core::cmp::Ordering, IrError> {
    let overflow = || IrError::ArithmeticOverflow { op: "real_cmp" };
    match (a, b) {
        (Value::Real(x), Value::Real(y)) => x.checked_cmp(y).ok_or_else(overflow),
        (Value::RealAlgebraic(x), Value::Real(y)) => x.compare_rational(y).ok_or_else(overflow),
        (Value::Real(x), Value::RealAlgebraic(y)) => {
            // α (y) vs c (x): flip the orientation of (c vs α).
            y.compare_rational(x)
                .map(core::cmp::Ordering::reverse)
                .ok_or_else(overflow)
        }
        (Value::RealAlgebraic(x), Value::RealAlgebraic(y)) => {
            algebraic_cmp(x, y).ok_or_else(overflow)
        }
        _ => panic!("real_cmp on non-real operands"),
    }
}

/// Exact ordering of two real algebraic numbers: equal (root-aware) ⇒ `Equal`;
/// otherwise refine both isolating intervals until disjoint and order by position.
/// Returns `None` on overflow or non-convergence (caller maps to overflow).
fn algebraic_cmp(
    x: &crate::real_algebraic::RealAlgebraic,
    y: &crate::real_algebraic::RealAlgebraic,
) -> Option<core::cmp::Ordering> {
    if x == y {
        return Some(core::cmp::Ordering::Equal);
    }
    // Distinct values: compare `x` against each endpoint of `y`'s interval to
    // locate it. `x` is one fixed root; `y`'s interval brackets a *different*
    // value, so comparing `x` to `y`'s rational endpoints decides the order once
    // `x` falls cleanly on one side. We refine `y`'s bracket via its endpoints.
    let (ylo, yhi) = y.interval_big();
    // If x ≤ ylo then x < y (x is below y's whole bracket); if x ≥ yhi then x > y.
    match x.compare_big(&ylo)? {
        core::cmp::Ordering::Less | core::cmp::Ordering::Equal => {
            return Some(core::cmp::Ordering::Less);
        }
        core::cmp::Ordering::Greater => {}
    }
    match x.compare_big(&yhi)? {
        core::cmp::Ordering::Greater | core::cmp::Ordering::Equal => {
            return Some(core::cmp::Ordering::Greater);
        }
        core::cmp::Ordering::Less => {}
    }
    // x lies strictly inside y's bracket but x != y: the values are distinct yet
    // both inside (lo, hi). Decline (overflow path) rather than guess — slice 1
    // does not need this case (the decider compares an algebraic witness only to
    // rationals). Sound: returns None → caller reports overflow → graceful unknown.
    None
}

/// The bit-vector width an operand value carries (`Bv`/`WideBv`), else `None`.
fn bv_width_of(v: &Value) -> Option<u32> {
    match v {
        Value::Bv { width, .. } => Some(*width),
        Value::WideBv(w) => Some(w.width()),
        _ => None,
    }
}

/// Whether `op` over `vals` yields a bit-vector wider than 128 bits — true only
/// for the width-growing operators (the rest preserve or shrink width, so a wide
/// result already implies a wide operand, caught separately).
fn result_exceeds_128(op: Op, vals: &[Value]) -> bool {
    match op {
        Op::ZeroExt { by } | Op::SignExt { by } => {
            bv_width_of(&vals[0]).is_some_and(|w| w + by > 128)
        }
        Op::Concat => {
            matches!((bv_width_of(&vals[0]), bv_width_of(&vals[1])), (Some(a), Some(b)) if a + b > 128)
        }
        Op::Int2Bv { width } => width > 128,
        _ => false,
    }
}

/// The wide (`> 128`-bit) bit-vector evaluation path, reached from [`apply`] only
/// when an operand is a [`Value::WideBv`]. Operands are normalized to
/// [`crate::wide::WideUint`] (a `Value::Bv` widens losslessly), the operator runs
/// via its validated `WideUint` implementation, and a `≤ 128`-bit result narrows
/// back to a `Value::Bv` (so the two representations never overlap).
#[allow(clippy::too_many_lines)]
fn apply_wide(op: Op, vals: &[Value]) -> Value {
    use crate::wide::WideUint;
    let w = |v: &Value| -> WideUint {
        match v {
            Value::WideBv(x) => x.clone(),
            Value::Bv { width, value } => WideUint::from_u128(*value, *width),
            _ => panic!("apply_wide on a non-bit-vector operand"),
        }
    };
    // Narrow a result back to `Value::Bv` when it fits 128 bits.
    let pack = |r: WideUint| -> Value {
        if r.width() <= 128 {
            Value::Bv {
                width: r.width(),
                value: r.to_u128(),
            }
        } else {
            Value::WideBv(r)
        }
    };
    // The shift amount (second operand) as a `u32`, saturated to the width.
    let shift_amount = |amount: &WideUint, width: u32| -> u32 {
        let width_w = WideUint::from_u128(u128::from(width), amount.width());
        if amount.uge(&width_w) {
            width
        } else {
            // amount < width fits a u32: read its low bits.
            let bits = amount.to_lsb_bits();
            let mut n = 0u32;
            for (i, &bit) in bits.iter().take(32).enumerate() {
                if bit {
                    n |= 1u32 << i;
                }
            }
            n
        }
    };
    let one_bit = |b: bool| Value::Bv {
        width: 1,
        value: u128::from(b),
    };
    match op {
        Op::BvNot => pack(w(&vals[0]).not()),
        Op::BvAnd => pack(w(&vals[0]).and(&w(&vals[1]))),
        Op::BvOr => pack(w(&vals[0]).or(&w(&vals[1]))),
        Op::BvXor => pack(w(&vals[0]).xor(&w(&vals[1]))),
        Op::BvNand => pack(w(&vals[0]).and(&w(&vals[1])).not()),
        Op::BvNor => pack(w(&vals[0]).or(&w(&vals[1])).not()),
        Op::BvXnor => pack(w(&vals[0]).xor(&w(&vals[1])).not()),
        Op::BvNeg => pack(w(&vals[0]).neg()),
        Op::BvAdd => pack(w(&vals[0]).add(&w(&vals[1]))),
        Op::BvSub => pack(w(&vals[0]).sub(&w(&vals[1]))),
        Op::BvMul => pack(w(&vals[0]).mul(&w(&vals[1]))),
        Op::BvUdiv => pack(w(&vals[0]).udiv(&w(&vals[1]))),
        Op::BvUrem => pack(w(&vals[0]).urem(&w(&vals[1]))),
        Op::BvSdiv => pack(w(&vals[0]).sdiv(&w(&vals[1]))),
        Op::BvSrem => pack(w(&vals[0]).srem(&w(&vals[1]))),
        Op::BvSmod => pack(w(&vals[0]).smod(&w(&vals[1]))),
        Op::BvShl => {
            let a = w(&vals[0]);
            let k = shift_amount(&w(&vals[1]), a.width());
            pack(a.shl(k))
        }
        Op::BvLshr => {
            let a = w(&vals[0]);
            let k = shift_amount(&w(&vals[1]), a.width());
            pack(a.lshr(k))
        }
        Op::BvAshr => {
            let a = w(&vals[0]);
            let k = shift_amount(&w(&vals[1]), a.width());
            pack(a.ashr(k))
        }
        Op::BvUlt => Value::Bool(w(&vals[0]).ult(&w(&vals[1]))),
        Op::BvUle => Value::Bool(w(&vals[0]).ule(&w(&vals[1]))),
        Op::BvUgt => Value::Bool(w(&vals[1]).ult(&w(&vals[0]))),
        Op::BvUge => Value::Bool(w(&vals[0]).uge(&w(&vals[1]))),
        Op::BvSlt => Value::Bool(w(&vals[0]).slt(&w(&vals[1]))),
        Op::BvSle => Value::Bool(w(&vals[0]).sle(&w(&vals[1]))),
        Op::BvSgt => Value::Bool(w(&vals[1]).slt(&w(&vals[0]))),
        Op::BvSge => Value::Bool(w(&vals[1]).sle(&w(&vals[0]))),
        Op::Eq => Value::Bool(w(&vals[0]) == w(&vals[1])),
        Op::BvComp => one_bit(w(&vals[0]) == w(&vals[1])),
        Op::Ite => {
            if vals[0].as_bool().expect("ite condition is Bool") {
                vals[1].clone()
            } else {
                vals[2].clone()
            }
        }
        Op::Extract { hi, lo } => pack(w(&vals[0]).extract(hi, lo)),
        Op::Concat => pack(w(&vals[0]).concat(&w(&vals[1]))),
        Op::ZeroExt { by } => pack(w(&vals[0]).zero_ext(by)),
        Op::SignExt { by } => pack(w(&vals[0]).sign_ext(by)),
        Op::RotateLeft { by } => {
            let a = w(&vals[0]);
            let k = by % a.width().max(1);
            pack(a.shl(k).or(&a.lshr(a.width() - k)))
        }
        Op::RotateRight { by } => {
            let a = w(&vals[0]);
            let k = by % a.width().max(1);
            pack(a.lshr(k).or(&a.shl(a.width() - k)))
        }
        // A floating-point reinterpret is identity on the bits.
        Op::FpFromBits { .. } => pack(w(&vals[0])),
        // `(_ int2bv width)` with width > 128: the integer mod 2^width as a
        // two's-complement wide value (low 128 bits, sign-extended).
        Op::Int2Bv { width } => {
            let x = vals[0].as_int().expect("int2bv operand is Int");
            #[allow(clippy::cast_sign_loss)]
            let low = WideUint::from_u128(x as u128, 128.min(width));
            pack(if width > 128 {
                low.sign_ext(width - 128)
            } else {
                low
            })
        }
        other => panic!("apply_wide: operator {other:?} not supported on wide bit-vectors"),
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

fn int_bin(
    vals: &[Value],
    what: &'static str,
    f: impl Fn(i128, i128) -> Option<i128>,
) -> Result<Value, IrError> {
    let x = vals[0].as_int().expect("builder guaranteed Int operand");
    let y = vals[1].as_int().expect("builder guaranteed Int operand");
    // An out-of-range result (e.g. `i128::MAX + 1`) is reported as overflow
    // rather than panicking — the evaluator is the soundness trust anchor.
    f(x, y)
        .map(Value::Int)
        .ok_or(IrError::ArithmeticOverflow { op: what })
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

#[cfg(test)]
mod overflow_tests {
    //! The evaluator is the soundness trust anchor: an out-of-range arithmetic
    //! result must become a graceful `Err(ArithmeticOverflow)` — never a panic,
    //! never a wrapped (wrong) value. Correct in-range results are unchanged.

    use super::{Assignment, eval};
    use crate::error::IrError;
    use crate::rational::Rational;
    use crate::{Sort, TermArena, Value};

    fn overflow(op: &'static str) -> IrError {
        IrError::ArithmeticOverflow { op }
    }

    #[test]
    fn bv2nat_128bit_high_bit_set_is_graceful_overflow() {
        // value = 2^127: a 128-bit BV with the high bit set. As a non-negative
        // integer this is > i128::MAX, so there is no i128 representation —
        // overflow, NOT a wrapped negative integer, NOT a panic.
        let mut arena = TermArena::new();
        let v = arena.bv_const(128, 1u128 << 127).unwrap();
        let t = arena.bv2nat(v).unwrap();
        assert_eq!(eval(&arena, t, &Assignment::new()), Err(overflow("bv2nat")));
    }

    #[test]
    fn bv2nat_127bit_max_is_correct_positive() {
        // A 127-bit all-ones value = 2^127 - 1 = i128::MAX: still exactly
        // representable, so bv2nat must succeed with the correct positive Int.
        let mut arena = TermArena::new();
        let v = arena.bv_const(127, (1u128 << 127) - 1).unwrap();
        let t = arena.bv2nat(v).unwrap();
        assert_eq!(
            eval(&arena, t, &Assignment::new()),
            Ok(Value::Int(i128::MAX))
        );
    }

    #[test]
    fn bv2nat_small_value_unchanged() {
        let mut arena = TermArena::new();
        let v = arena.bv_const(8, 200).unwrap();
        let t = arena.bv2nat(v).unwrap();
        assert_eq!(eval(&arena, t, &Assignment::new()), Ok(Value::Int(200)));
    }

    #[test]
    fn bv2nat_wide_high_bit_set_is_graceful_overflow() {
        // A 256-bit all-ones value (≫ i128::MAX): bv2nat of a WIDE operand crosses
        // BV → Int. It must report overflow gracefully, NEVER panic on the wide
        // path (regression for the missing `apply_wide` Bv2Nat arm).
        let mut arena = TermArena::new();
        let v = arena.wide_bv_const(crate::wide::WideUint::ones(256));
        let t = arena.bv2nat(v).unwrap();
        assert_eq!(eval(&arena, t, &Assignment::new()), Err(overflow("bv2nat")));
    }

    #[test]
    fn bv2nat_wide_small_value_is_exact() {
        // A 256-bit value whose only set bits are low (42): it fits a non-negative
        // i128, so bv2nat must succeed exactly — not over-conservatively overflow.
        let mut arena = TermArena::new();
        let v = arena.wide_bv_const(crate::wide::WideUint::from_u128(42, 256));
        let t = arena.bv2nat(v).unwrap();
        assert_eq!(eval(&arena, t, &Assignment::new()), Ok(Value::Int(42)));
    }

    #[test]
    fn int_mul_overflow_is_graceful() {
        let mut arena = TermArena::new();
        let a = arena.int_const(i128::MAX);
        let b = arena.int_const(2);
        let t = arena.int_mul(a, b).unwrap();
        assert_eq!(
            eval(&arena, t, &Assignment::new()),
            Err(overflow("int_mul"))
        );
    }

    #[test]
    fn int_add_overflow_is_graceful() {
        let mut arena = TermArena::new();
        let a = arena.int_const(i128::MAX);
        let b = arena.int_const(1);
        let t = arena.int_add(a, b).unwrap();
        assert_eq!(
            eval(&arena, t, &Assignment::new()),
            Err(overflow("int_add"))
        );
    }

    #[test]
    fn int_neg_of_min_is_graceful() {
        let mut arena = TermArena::new();
        let a = arena.int_const(i128::MIN);
        let t = arena.int_neg(a).unwrap();
        assert_eq!(
            eval(&arena, t, &Assignment::new()),
            Err(overflow("int_neg"))
        );
    }

    #[test]
    fn int_abs_of_min_is_graceful() {
        let mut arena = TermArena::new();
        let a = arena.int_const(i128::MIN);
        let t = arena.int_abs(a).unwrap();
        assert_eq!(
            eval(&arena, t, &Assignment::new()),
            Err(overflow("int_abs"))
        );
    }

    #[test]
    fn int_arithmetic_in_range_unchanged() {
        let mut arena = TermArena::new();
        let a = arena.int_const(6);
        let b = arena.int_const(7);
        let t = arena.int_mul(a, b).unwrap();
        assert_eq!(eval(&arena, t, &Assignment::new()), Ok(Value::Int(42)));
    }

    #[test]
    fn real_mul_overflow_is_graceful() {
        // (i128::MAX / 1) * (i128::MAX / 1): numerator overflows i128.
        let mut arena = TermArena::new();
        let a = arena.real_const(Rational::integer(i128::MAX));
        let b = arena.real_const(Rational::integer(i128::MAX));
        let t = arena.real_mul(a, b).unwrap();
        assert_eq!(
            eval(&arena, t, &Assignment::new()),
            Err(overflow("real_mul"))
        );
    }

    #[test]
    fn real_neg_of_min_is_graceful() {
        let mut arena = TermArena::new();
        let a = arena.real_const(Rational::integer(i128::MIN));
        let t = arena.real_neg(a).unwrap();
        assert_eq!(
            eval(&arena, t, &Assignment::new()),
            Err(overflow("real_neg"))
        );
    }

    #[test]
    fn real_add_overflow_is_graceful() {
        // 1/(i128::MAX) + 1/2 cross-multiplies a huge denominator → overflow.
        let mut arena = TermArena::new();
        let a = arena.real_const(Rational::new(1, i128::MAX));
        let b = arena.real_const(Rational::new(1, 2));
        let t = arena.real_add(a, b).unwrap();
        assert_eq!(
            eval(&arena, t, &Assignment::new()),
            Err(overflow("real_add"))
        );
    }

    #[test]
    fn real_arithmetic_in_range_unchanged() {
        let mut arena = TermArena::new();
        let a = arena.real_const(Rational::new(1, 3));
        let b = arena.real_const(Rational::new(1, 6));
        let t = arena.real_add(a, b).unwrap();
        assert_eq!(
            eval(&arena, t, &Assignment::new()),
            Ok(Value::Real(Rational::new(1, 2)))
        );
    }

    #[test]
    fn wide_bv_arithmetic_does_not_overflow() {
        // A 200-bit add is mod-2^200: still infallible (no Int crossing), so it
        // must succeed (the Ok-wrapping of the wide path didn't break it).
        let mut arena = TermArena::new();
        let a = arena.bv_const(200, 5).unwrap();
        let b = arena.bv_const(200, 7).unwrap();
        let t = arena.bv_add(a, b).unwrap();
        let result = eval(&arena, t, &Assignment::new()).unwrap();
        // 5 + 7 = 12 at width 200.
        let expected = arena.bv_const(200, 12).unwrap();
        let expected_v = eval(&arena, expected, &Assignment::new()).unwrap();
        assert_eq!(result, expected_v);
        // Sanity: it is a bit-vector of width 200.
        assert!(matches!(arena.sort_of(t), Sort::BitVec(200)));
    }
}

#[cfg(test)]
mod eval_with_memo_tests {
    use std::collections::HashMap;

    use super::{Assignment, eval, eval_with_memo};
    use crate::{Sort, TermArena, Value};

    /// `eval_with_memo` with an empty memo equals `eval`; and reusing a persistent
    /// memo across an assignment change — with the changed symbol's dependent
    /// subterms invalidated — yields the same value as a fresh `eval` (the
    /// incremental contract).
    #[test]
    fn incremental_memo_matches_fresh_eval() {
        let mut arena = TermArena::new();
        let x = arena.declare("x", Sort::BitVec(8)).unwrap();
        let y = arena.declare("y", Sort::BitVec(8)).unwrap();
        let (xv, yv) = (arena.var(x), arena.var(y));
        let sum = arena.bv_add(xv, yv).unwrap(); // depends on x and y
        let ten = arena.bv_const(8, 10).unwrap();
        let goal = arena.eq(sum, ten).unwrap(); // (x + y) == 10

        let mut asg = Assignment::new();
        asg.set(x, Value::Bv { width: 8, value: 3 });
        asg.set(y, Value::Bv { width: 8, value: 7 });

        // Empty memo == eval; memo is populated with subterm values.
        let mut memo: HashMap<_, _> = HashMap::new();
        let inc = eval_with_memo(&arena, goal, &asg, &mut memo).unwrap();
        assert_eq!(inc, eval(&arena, goal, &asg).unwrap());
        assert_eq!(inc, Value::Bool(true)); // 3 + 7 == 10

        // Change x := 4. Invalidate the cone of x — its own symbol node `xv` PLUS
        // every subterm depending on it (`sum`, `goal`); `y` and the constant are
        // reused. (Forgetting `xv` would silently reuse the stale x=3 value — the
        // invalidation contract includes the changed symbol's own node.) The
        // incremental result must equal a fresh eval over the new assignment.
        asg.set(x, Value::Bv { width: 8, value: 4 });
        memo.remove(&xv);
        memo.remove(&sum);
        memo.remove(&goal);
        let inc2 = eval_with_memo(&arena, goal, &asg, &mut memo).unwrap();
        assert_eq!(inc2, eval(&arena, goal, &asg).unwrap());
        assert_eq!(inc2, Value::Bool(false)); // 4 + 7 == 11 ≠ 10
    }
}
