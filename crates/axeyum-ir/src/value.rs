//! Concrete values produced by evaluation and carried by models.

use std::collections::BTreeMap;

use crate::rational::Rational;
use crate::sort::Sort;
use crate::term::{ConstructorId, DatatypeId};

/// A concrete value of some [`Sort`].
///
/// `Value` is `Clone` but not `Copy`: array values (ADR-0010) carry a map and
/// therefore cannot be `Copy`. Scalar `Bool`/`Bv` values are cheap to clone.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Value {
    /// A Boolean value.
    Bool(bool),
    /// A bit-vector value of width `≤ 128`; `value` always fits in `width` bits.
    /// Wider bit-vectors are [`Value::WideBv`]; the two never overlap.
    Bv {
        /// Width in bits.
        width: u32,
        /// The value, masked to `width` bits.
        value: u128,
    },
    /// A bit-vector value of width `> 128`, stored as limbs (wide-BV).
    WideBv(crate::wide::WideUint),
    /// An array value: a total map from `BitVec(index)` to `BitVec(element)`,
    /// stored as a default element plus the overriding entries.
    Array(ArrayValue),
    /// A mathematical integer value (ADR-0014); exact within the `i128`
    /// reference range.
    Int(i128),
    /// A mathematical real value as an exact rational (ADR-0015).
    Real(Rational),
    /// A real *algebraic* value — possibly irrational — as a defining integer
    /// polynomial plus an isolating interval (ADR-0038). The denoted value is the
    /// unique real root of the polynomial inside the interval; e.g. `√2` is the
    /// root of `x² − 2` in `(1, 2)`. Slice 1 supports sign/comparison only; field
    /// arithmetic on this variant is deferred.
    RealAlgebraic(crate::real_algebraic::RealAlgebraic),
    /// A datatype value: its constructor and field values (a `Clone` tree, like
    /// [`ArrayValue`]); ADR-0022.
    Datatype {
        /// The datatype this value belongs to.
        datatype: DatatypeId,
        /// The constructor used to build it.
        constructor: ConstructorId,
        /// The field values, in constructor-declaration order.
        fields: Vec<Value>,
    },
}

/// A concrete array value: a default element plus index→element overrides.
///
/// The map is kept normalized — entries equal to `default` are removed — so
/// equality is extensional and the representation is deterministic.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ArrayValue {
    index_width: u32,
    element_width: u32,
    default: u128,
    entries: BTreeMap<u128, u128>,
}

impl ArrayValue {
    /// Creates a constant array mapping every index to `default`.
    pub fn constant(index_width: u32, element_width: u32, default: u128) -> Self {
        Self {
            index_width,
            element_width,
            default: default & mask(element_width),
            entries: BTreeMap::new(),
        }
    }

    /// The index bit-vector width.
    pub fn index_width(&self) -> u32 {
        self.index_width
    }

    /// The element bit-vector width.
    pub fn element_width(&self) -> u32 {
        self.element_width
    }

    /// The element value at `index`.
    pub fn select(&self, index: u128) -> u128 {
        let index = index & mask(self.index_width);
        self.entries.get(&index).copied().unwrap_or(self.default)
    }

    /// Returns a copy of this array with `index` mapped to `element`.
    #[must_use]
    pub fn store(&self, index: u128, element: u128) -> Self {
        let index = index & mask(self.index_width);
        let element = element & mask(self.element_width);
        let mut entries = self.entries.clone();
        if element == self.default {
            entries.remove(&index);
        } else {
            entries.insert(index, element);
        }
        Self {
            index_width: self.index_width,
            element_width: self.element_width,
            default: self.default,
            entries,
        }
    }

    /// The default element value.
    pub fn default_element(&self) -> u128 {
        self.default
    }

    /// The overriding `(index, element)` entries in index order.
    pub fn entries(&self) -> impl Iterator<Item = (u128, u128)> + '_ {
        self.entries.iter().map(|(&i, &e)| (i, e))
    }
}

/// A concrete interpretation of an uninterpreted function (ADR-0013): a total
/// map from argument tuples to a result, stored as a default result plus the
/// overriding entries.
///
/// Two storage modes coexist:
///
/// * **Scalar** (`Bool`/`BitVec`/`Float` parameters *and* result): both keys and
///   results are encoded to `u128` (a `Bool` as `0`/`1`, a `BitVec`/`Float`
///   masked to its width). This is the original ADR-0013 path; entries are kept
///   in a normalized [`BTreeMap`] — entries equal to `default` are removed.
/// * **Arithmetic** (`Int`/`Real` appearing in a parameter or the result): keys
///   and results are full [`Value`]s, since integers and reals have no `u128`
///   scalar code (the `QF_UFLIA`/`QF_UFLRA` witnessing-model path, kept finite —
///   only the argument tuples the query actually constrains are recorded, plus a
///   default for every other point). `Value` is `Eq` but not `Ord`, so these
///   entries are an insertion-deduplicated [`Vec`]; iteration order is the order
///   the entries were defined (deterministic for a deterministic projection).
///
/// In both modes the map is normalized — entries equal to the default are
/// removed — so equality is extensional and the representation deterministic.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FuncValue {
    params: Vec<Sort>,
    result: Sort,
    storage: FuncStorage,
}

/// The backing store of a [`FuncValue`]: scalar (`u128`-coded) or arithmetic
/// (full-[`Value`]-keyed) — see [`FuncValue`].
#[derive(Debug, Clone, PartialEq, Eq)]
enum FuncStorage {
    /// `u128`-coded keys and results (`Bool`/`BitVec`/`Float`).
    Scalar {
        default: u128,
        entries: BTreeMap<Vec<u128>, u128>,
    },
    /// Full-[`Value`]-keyed keys and results (`Int`/`Real` present); entries are
    /// an insertion-deduplicated [`Vec`] because [`Value`] is not `Ord`.
    Arith {
        default: Value,
        entries: Vec<(Vec<Value>, Value)>,
    },
}

/// Whether `sort` is an arithmetic sort (`Int`/`Real`) that has no `u128`
/// scalar code and therefore requires the [`FuncStorage::Arith`] path.
fn is_arith_sort(sort: Sort) -> bool {
    matches!(sort, Sort::Int | Sort::Real)
}

impl FuncValue {
    /// Whether any parameter or the result sort is arithmetic (`Int`/`Real`), so
    /// this interpretation uses the full-[`Value`]-keyed [`FuncStorage::Arith`]
    /// path rather than the `u128` scalar path.
    fn sorts_are_arith(params: &[Sort], result: Sort) -> bool {
        params.iter().copied().any(is_arith_sort) || is_arith_sort(result)
    }

    /// Creates a constant scalar function mapping every argument tuple to
    /// `default`.
    ///
    /// # Panics
    ///
    /// Panics if any parameter or the result sort is an array, or is arithmetic
    /// (`Int`/`Real`) — arithmetic interpretations must use
    /// [`FuncValue::constant_value`].
    pub fn constant(params: Vec<Sort>, result: Sort, default: u128) -> Self {
        assert!(
            params.iter().all(|s| !matches!(s, Sort::Array { .. }))
                && !matches!(result, Sort::Array { .. }),
            "function arguments and result must be scalar"
        );
        assert!(
            !Self::sorts_are_arith(&params, result),
            "arithmetic-sorted functions must use FuncValue::constant_value"
        );
        Self {
            storage: FuncStorage::Scalar {
                default: encode_to(result, default),
                entries: BTreeMap::new(),
            },
            params,
            result,
        }
    }

    /// Creates a constant arithmetic (`Int`/`Real`) function mapping every
    /// argument tuple to `default`. The default is any value of the result sort;
    /// the original query only constrains the explicitly defined points.
    ///
    /// # Panics
    ///
    /// Panics if neither a parameter nor the result is arithmetic (use
    /// [`FuncValue::constant`] for purely scalar functions), or if `default`'s
    /// sort does not match `result`.
    pub fn constant_value(params: Vec<Sort>, result: Sort, default: Value) -> Self {
        assert!(
            Self::sorts_are_arith(&params, result),
            "FuncValue::constant_value is for arithmetic-sorted functions"
        );
        assert_eq!(
            default.sort(),
            result,
            "default value sort must match the function result sort"
        );
        Self {
            storage: FuncStorage::Arith {
                default,
                entries: Vec::new(),
            },
            params,
            result,
        }
    }

    /// The parameter sorts, in argument order.
    pub fn params(&self) -> &[Sort] {
        &self.params
    }

    /// The result sort.
    pub fn result(&self) -> Sort {
        self.result
    }

    /// Whether this interpretation uses the full-[`Value`]-keyed arithmetic
    /// storage path.
    pub fn is_arith(&self) -> bool {
        matches!(self.storage, FuncStorage::Arith { .. })
    }

    /// The encoded result for `args` (each argument encoded to `u128`).
    ///
    /// # Panics
    ///
    /// Panics if `args` does not match the declared arity, or if this is an
    /// arithmetic-storage interpretation (use [`FuncValue::apply_value`]).
    pub fn apply(&self, args: &[u128]) -> u128 {
        match &self.storage {
            FuncStorage::Scalar { default, entries } => {
                let key = self.normalize_key(args);
                entries.get(&key).copied().unwrap_or(*default)
            }
            FuncStorage::Arith { .. } => {
                panic!("FuncValue::apply on an arithmetic-storage function (use apply_value)")
            }
        }
    }

    /// The result [`Value`] for `args` (full-value keys). Works for both storage
    /// modes: for scalar storage the arguments and result are `u128`-coded
    /// internally.
    ///
    /// # Panics
    ///
    /// Panics if `args` does not match the declared arity, or (scalar mode) if an
    /// argument value is not scalar-codable.
    pub fn apply_value(&self, args: &[Value]) -> Value {
        assert_eq!(args.len(), self.params.len(), "function arity mismatch");
        match &self.storage {
            FuncStorage::Scalar { default, entries } => {
                let key: Vec<u128> = self
                    .params
                    .iter()
                    .zip(args)
                    .map(|(&sort, arg)| encode_to(sort, arg.scalar_code()))
                    .collect();
                let code = entries.get(&key).copied().unwrap_or(*default);
                Value::from_scalar_code(self.result, code)
            }
            FuncStorage::Arith { default, entries } => entries
                .iter()
                .find(|(k, _)| k.as_slice() == args)
                .map_or_else(|| default.clone(), |(_, v)| v.clone()),
        }
    }

    /// Returns a copy of this scalar function with `args` mapped to `result`.
    ///
    /// # Panics
    ///
    /// Panics if `args` does not match the declared arity, or if this is an
    /// arithmetic-storage interpretation (use [`FuncValue::define_value`]).
    #[must_use]
    pub fn define(&self, args: &[u128], result: u128) -> Self {
        let FuncStorage::Scalar { default, entries } = &self.storage else {
            panic!("FuncValue::define on an arithmetic-storage function (use define_value)");
        };
        let key = self.normalize_key(args);
        let result = encode_to(self.result, result);
        let mut entries = entries.clone();
        if result == *default {
            entries.remove(&key);
        } else {
            entries.insert(key, result);
        }
        Self {
            params: self.params.clone(),
            result: self.result,
            storage: FuncStorage::Scalar {
                default: *default,
                entries,
            },
        }
    }

    /// Returns a copy of this arithmetic function with the `args` tuple mapped to
    /// `result` (full [`Value`] keys/results). An entry equal to the default is
    /// dropped (normalization); redefining an existing tuple replaces it
    /// in place (preserving order).
    ///
    /// # Panics
    ///
    /// Panics if `args` does not match the declared arity, if this is a
    /// scalar-storage interpretation (use [`FuncValue::define`]), or if a key or
    /// the result has the wrong sort.
    #[must_use]
    pub fn define_value(&self, args: &[Value], result: Value) -> Self {
        let FuncStorage::Arith { default, entries } = &self.storage else {
            panic!("FuncValue::define_value on a scalar-storage function (use define)");
        };
        assert_eq!(args.len(), self.params.len(), "function arity mismatch");
        for (&sort, arg) in self.params.iter().zip(args) {
            assert_eq!(
                arg.sort(),
                sort,
                "argument sort must match the parameter sort"
            );
        }
        assert_eq!(
            result.sort(),
            self.result,
            "result sort must match the function result sort"
        );
        let key: Vec<Value> = args.to_vec();
        let mut entries = entries.clone();
        if let Some(pos) = entries.iter().position(|(k, _)| *k == key) {
            if result == *default {
                entries.remove(pos);
            } else {
                entries[pos].1 = result;
            }
        } else if result != *default {
            entries.push((key, result));
        }
        Self {
            params: self.params.clone(),
            result: self.result,
            storage: FuncStorage::Arith {
                default: default.clone(),
                entries,
            },
        }
    }

    /// The default (encoded) result value (scalar storage).
    ///
    /// # Panics
    ///
    /// Panics for an arithmetic-storage interpretation (use
    /// [`FuncValue::default_value`]).
    pub fn default_result(&self) -> u128 {
        match &self.storage {
            FuncStorage::Scalar { default, .. } => *default,
            FuncStorage::Arith { .. } => {
                panic!("FuncValue::default_result on an arithmetic-storage function")
            }
        }
    }

    /// The default result [`Value`] (works for both storage modes).
    pub fn default_value(&self) -> Value {
        match &self.storage {
            FuncStorage::Scalar { default, .. } => Value::from_scalar_code(self.result, *default),
            FuncStorage::Arith { default, .. } => default.clone(),
        }
    }

    /// The overriding `(args, result)` entries in argument-tuple order (scalar
    /// storage only).
    ///
    /// # Panics
    ///
    /// Panics for an arithmetic-storage interpretation (use
    /// [`FuncValue::value_entries`]).
    pub fn entries(&self) -> impl Iterator<Item = (&[u128], u128)> + '_ {
        let FuncStorage::Scalar { entries, .. } = &self.storage else {
            panic!("FuncValue::entries on an arithmetic-storage function (use value_entries)");
        };
        entries.iter().map(|(k, &v)| (k.as_slice(), v))
    }

    /// The overriding `(args, result)` entries as full [`Value`]s, in definition
    /// order (arithmetic storage only).
    pub fn value_entries(&self) -> impl Iterator<Item = (&[Value], &Value)> + '_ {
        let entries: &[(Vec<Value>, Value)] = match &self.storage {
            FuncStorage::Arith { entries, .. } => entries,
            FuncStorage::Scalar { .. } => &[],
        };
        entries.iter().map(|(k, v)| (k.as_slice(), v))
    }

    fn normalize_key(&self, args: &[u128]) -> Vec<u128> {
        assert_eq!(args.len(), self.params.len(), "function arity mismatch");
        self.params
            .iter()
            .zip(args)
            .map(|(&sort, &arg)| encode_to(sort, arg))
            .collect()
    }
}

/// Encodes a raw scalar `value` to the canonical `u128` for `sort`: a `Bool` as
/// `0`/`1`, a `BitVec` masked to its width.
///
/// # Panics
///
/// Panics if `sort` is an array.
fn encode_to(sort: Sort, value: u128) -> u128 {
    match sort {
        Sort::Bool => u128::from(value != 0),
        Sort::BitVec(w) => value & mask(w),
        // Floating-point values are represented as their `exp + sig`-bit pattern.
        Sort::Float { exp, sig } => value & mask(exp + sig),
        Sort::Array { .. } => panic!("scalar encoding of an array sort"),
        Sort::Int => panic!("scalar encoding of an integer sort"),
        Sort::Real => panic!("scalar encoding of a real sort"),
        Sort::Datatype(_) => panic!("scalar encoding of a datatype sort"),
    }
}

impl Value {
    /// The scalar (`Bool`/`BitVec`) value carried by `code` interpreted at
    /// `sort`: a `Bool` if `sort` is `Bool`, otherwise a width-`w` bit-vector.
    ///
    /// # Panics
    ///
    /// Panics if `sort` is an array.
    pub fn from_scalar_code(sort: Sort, code: u128) -> Value {
        match sort {
            Sort::Bool => Value::Bool(code != 0),
            Sort::BitVec(w) => Value::Bv {
                width: w,
                value: code & mask(w),
            },
            // A floating-point value decodes as its `exp + sig`-bit pattern.
            Sort::Float { exp, sig } => Value::Bv {
                width: exp + sig,
                value: code & mask(exp + sig),
            },
            Sort::Array { .. } => panic!("scalar decoding of an array sort"),
            Sort::Int => panic!("scalar decoding of an integer sort"),
            // A real sort never decodes from a scalar code (real values — rational
            // or algebraic — are not scalar bit patterns).
            Sort::Real => panic!("scalar decoding of a real sort"),
            Sort::Datatype(_) => panic!("scalar decoding of a datatype sort"),
        }
    }

    /// Encodes this scalar value to its canonical `u128` (a `Bool` as `0`/`1`,
    /// a `BitVec` as its masked value).
    ///
    /// # Panics
    ///
    /// Panics if this is an array value.
    pub fn scalar_code(&self) -> u128 {
        match self {
            Value::Bool(b) => u128::from(*b),
            Value::Bv { value, .. } => *value,
            Value::WideBv(_) => panic!("scalar encoding of a >128-bit bit-vector value"),
            Value::Array(_) => panic!("scalar encoding of an array value"),
            Value::Int(_) => panic!("scalar encoding of an integer value"),
            Value::Real(_) => panic!("scalar encoding of a real value"),
            Value::RealAlgebraic(_) => panic!("scalar encoding of a real-algebraic value"),
            Value::Datatype { .. } => panic!("scalar encoding of a datatype value"),
        }
    }

    /// The sort of this value.
    pub fn sort(&self) -> Sort {
        match self {
            Value::Bool(_) => Sort::Bool,
            Value::Bv { width, .. } => Sort::BitVec(*width),
            Value::WideBv(w) => Sort::BitVec(w.width()),
            Value::Array(array) => Sort::Array {
                index: array.index_width,
                element: array.element_width,
            },
            Value::Int(_) => Sort::Int,
            Value::Real(_) | Value::RealAlgebraic(_) => Sort::Real,
            Value::Datatype { datatype, .. } => Sort::Datatype(*datatype),
        }
    }

    /// Returns the Boolean payload, or `None` for non-Boolean values.
    pub fn as_bool(&self) -> Option<bool> {
        match self {
            Value::Bool(b) => Some(*b),
            Value::Bv { .. }
            | Value::Array(_)
            | Value::Int(_)
            | Value::Real(_)
            | Value::RealAlgebraic(_)
            | Value::Datatype { .. }
            | Value::WideBv(_) => None,
        }
    }

    /// Returns the bit-vector payload `(width, value)`, or `None`.
    pub fn as_bv(&self) -> Option<(u32, u128)> {
        match self {
            Value::Bv { width, value } => Some((*width, *value)),
            Value::Bool(_)
            | Value::Array(_)
            | Value::Int(_)
            | Value::Real(_)
            | Value::RealAlgebraic(_)
            | Value::Datatype { .. }
            | Value::WideBv(_) => None,
        }
    }

    /// Returns the array payload, or `None` for non-array values.
    pub fn as_array(&self) -> Option<&ArrayValue> {
        match self {
            Value::Array(array) => Some(array),
            Value::Bool(_)
            | Value::Bv { .. }
            | Value::Int(_)
            | Value::Real(_)
            | Value::RealAlgebraic(_)
            | Value::Datatype { .. }
            | Value::WideBv(_) => None,
        }
    }

    /// Returns the integer payload, or `None` for non-integer values.
    pub fn as_int(&self) -> Option<i128> {
        match self {
            Value::Int(value) => Some(*value),
            Value::Bool(_)
            | Value::Bv { .. }
            | Value::Array(_)
            | Value::Real(_)
            | Value::RealAlgebraic(_)
            | Value::Datatype { .. }
            | Value::WideBv(_) => None,
        }
    }

    /// Returns the real (rational) payload, or `None` for non-real values.
    ///
    /// A [`Value::RealAlgebraic`] is real-sorted but *not* a plain rational, so
    /// this returns `None` for it — callers needing exact handling of an algebraic
    /// real must dispatch on [`Value::as_real_algebraic`] instead.
    pub fn as_real(&self) -> Option<Rational> {
        match self {
            Value::Real(value) => Some(*value),
            Value::Bool(_)
            | Value::Bv { .. }
            | Value::Array(_)
            | Value::Int(_)
            | Value::RealAlgebraic(_)
            | Value::Datatype { .. }
            | Value::WideBv(_) => None,
        }
    }

    /// Returns the real-algebraic payload, or `None` for any other value
    /// (including a plain rational [`Value::Real`]).
    pub fn as_real_algebraic(&self) -> Option<&crate::real_algebraic::RealAlgebraic> {
        match self {
            Value::RealAlgebraic(a) => Some(a),
            _ => None,
        }
    }

    /// Returns the wide (`> 128`-bit) bit-vector payload, or `None`.
    pub fn as_wide_bv(&self) -> Option<&crate::wide::WideUint> {
        match self {
            Value::WideBv(w) => Some(w),
            _ => None,
        }
    }
}

impl core::fmt::Display for Value {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Value::Bool(b) => write!(f, "{b}"),
            Value::Bv { width, value } => {
                write!(f, "#x{value:0>pad$x}", pad = (*width as usize).div_ceil(4))
            }
            Value::WideBv(w) => {
                // Render MSB-first as a binary literal (no u128 to hex-format).
                write!(f, "#b")?;
                for i in (0..w.width()).rev() {
                    write!(f, "{}", u8::from(w.bit(i)))?;
                }
                Ok(())
            }
            Value::Array(array) => {
                write!(f, "(array default #x{:x}", array.default)?;
                for (index, element) in array.entries() {
                    write!(f, " [#x{index:x} -> #x{element:x}]")?;
                }
                write!(f, ")")
            }
            Value::Int(value) => write!(f, "{value}"),
            Value::Real(value) => write!(f, "{value}"),
            Value::RealAlgebraic(value) => write!(f, "{value}"),
            Value::Datatype {
                constructor,
                fields,
                ..
            } => {
                write!(f, "(construct/{}", constructor.index())?;
                for field in fields {
                    write!(f, " {field}")?;
                }
                write!(f, ")")
            }
        }
    }
}

fn mask(width: u32) -> u128 {
    if width >= 128 {
        u128::MAX
    } else {
        (1u128 << width) - 1
    }
}
