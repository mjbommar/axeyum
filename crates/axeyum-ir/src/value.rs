//! Concrete values produced by evaluation and carried by models.

use std::collections::BTreeMap;

use crate::rational::Rational;
use crate::sort::{ArraySortKey, Sort, SortId};
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
    /// A bit-vector array value: a total map from `BitVec(index)` to
    /// `BitVec(element)`, stored as a default element plus the overriding entries.
    Array(ArrayValue),
    /// A generic non-BV array value, keyed by full [`Value`]s. This is used for
    /// first-class array component sorts such as `(Array Int Int)`; the legacy
    /// [`Value::Array`] path remains the compact representation for pure BV
    /// arrays.
    GenericArray(GenericArrayValue),
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
    /// A value of an uninterpreted carrier sort. The token has no arithmetic
    /// meaning; it is only compared for equality within the same declared sort.
    Uninterpreted {
        /// The declared carrier sort.
        sort: SortId,
        /// A deterministic model token for one equivalence class.
        value: u128,
    },
    /// A concrete sequence value (ADR-0051, P2.7): the ordered element values.
    /// The empty sequence is `Seq(vec![])`; a `str.unit(x)` value is
    /// `Seq(vec![x])`. All elements share the sequence's scalar element sort.
    Seq(Vec<Value>),
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

/// A concrete array value over arbitrary non-array component sorts.
///
/// Entries are stored as full [`Value`] pairs because `Int`, `Real`,
/// datatypes, and declared uninterpreted carriers are not all `u128`-codable.
/// `Value` is not ordered, so the representation is an insertion-deduplicated
/// vector. Entries are sorted by a deterministic value key after every update, so
/// equality is extensional for the represented finite override set; entries equal
/// to the default are removed and redefinitions replace in place.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct GenericArrayValue {
    index: ArraySortKey,
    element: ArraySortKey,
    default: Box<Value>,
    entries: Vec<(Value, Value)>,
}

impl GenericArrayValue {
    /// Creates a constant array mapping every index to `default`.
    ///
    /// # Panics
    ///
    /// Panics if `default` does not have the array element sort.
    pub fn constant(index: ArraySortKey, element: ArraySortKey, default: Value) -> Self {
        let default = canonicalize_for_sort(element.to_sort(), default);
        assert!(
            value_matches_sort(&default, element.to_sort()),
            "generic array default sort must match element sort"
        );
        Self {
            index,
            element,
            default: Box::new(default),
            entries: Vec::new(),
        }
    }

    /// The index component sort.
    pub fn index_sort(&self) -> ArraySortKey {
        self.index
    }

    /// The element component sort.
    pub fn element_sort(&self) -> ArraySortKey {
        self.element
    }

    /// The default element value.
    pub fn default_value(&self) -> &Value {
        &self.default
    }

    /// The element value at `index`.
    ///
    /// # Panics
    ///
    /// Panics if `index` does not have the array index sort.
    pub fn select(&self, index: &Value) -> Value {
        assert!(
            value_matches_sort(index, self.index.to_sort()),
            "generic array index sort mismatch"
        );
        let index = canonicalize_for_sort(self.index.to_sort(), index.clone());
        self.entries
            .iter()
            .find(|(i, _)| *i == index)
            .map_or_else(|| (*self.default).clone(), |(_, v)| v.clone())
    }

    /// Returns a copy of this array with `index` mapped to `element`.
    ///
    /// # Panics
    ///
    /// Panics if `index` or `element` has the wrong component sort.
    #[must_use]
    pub fn store(&self, index: Value, element: Value) -> Self {
        assert!(
            value_matches_sort(&index, self.index.to_sort()),
            "generic array index sort mismatch"
        );
        assert!(
            value_matches_sort(&element, self.element.to_sort()),
            "generic array element sort mismatch"
        );
        let index = canonicalize_for_sort(self.index.to_sort(), index);
        let element = canonicalize_for_sort(self.element.to_sort(), element);
        let mut entries = self.entries.clone();
        if let Some(pos) = entries.iter().position(|(i, _)| *i == index) {
            if element == *self.default {
                entries.remove(pos);
            } else {
                entries[pos].1 = element;
            }
        } else if element != *self.default {
            entries.push((index, element));
        }
        normalize_generic_array_entries(&mut entries);
        Self {
            index: self.index,
            element: self.element,
            default: self.default.clone(),
            entries,
        }
    }

    /// The overriding `(index, element)` entries in deterministic projection
    /// order.
    pub fn entries(&self) -> impl Iterator<Item = (&Value, &Value)> + '_ {
        self.entries.iter().map(|(i, e)| (i, e))
    }
}

fn normalize_generic_array_entries(entries: &mut [(Value, Value)]) {
    entries.sort_by_key(|(index, _)| value_order_key(index));
}

fn value_order_key(value: &Value) -> String {
    format!("{}:{value}", value.sort())
}

/// A concrete interpretation of an uninterpreted function (ADR-0013): a total
/// map from argument tuples to a result, stored as a default result plus the
/// overriding entries.
///
/// Two storage modes coexist:
///
/// * **Scalar** (`Bool`/`BitVec<=128`/`Float<=128`/uninterpreted parameters *and* result):
///   both keys and results are encoded to `u128` (a `Bool` as `0`/`1`, a
///   `BitVec`/`Float` masked to its width, an uninterpreted value as its model
///   token). This is the original ADR-0013 path extended to many-sorted EUF;
///   entries are kept in a normalized [`BTreeMap`] — entries equal to `default`
///   are removed.
/// * **Full-value** (wide `BitVec`/`Float`, `Int`/`Real`/array/datatype appearing in a parameter or the
///   result): keys and results are full [`Value`]s, since those sorts have no
///   scalar `u128` code (the `QF_UFLIA`/`QF_UFLRA` witnessing-model path, plus
///   mixed UF/array signatures). The table is kept finite — only the argument
///   tuples the query actually constrains are recorded, plus a default for every
///   other point. `Value` is `Eq` but not `Ord`, so these entries are an
///   insertion-deduplicated [`Vec`]; iteration order is the order the entries
///   were defined (deterministic for a deterministic projection).
///
/// In both modes the map is normalized — entries equal to the default are
/// removed — so equality is extensional and the representation deterministic.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FuncValue {
    params: Vec<Sort>,
    result: Sort,
    storage: FuncStorage,
}

/// The backing store of a [`FuncValue`]: scalar (`u128`-coded) or full-value
/// (full-[`Value`]-keyed) — see [`FuncValue`].
#[derive(Debug, Clone, PartialEq, Eq)]
enum FuncStorage {
    /// `u128`-coded keys and results (`Bool`/`BitVec<=128`/`Float<=128`/uninterpreted).
    Scalar {
        default: u128,
        entries: BTreeMap<Vec<u128>, u128>,
    },
    /// Full-[`Value`]-keyed keys and results (wide `BitVec`/`Float`,
    /// `Int`/`Real`/array/datatype present); entries are an
    /// insertion-deduplicated [`Vec`] because [`Value`] is not `Ord`.
    FullValue {
        default: Value,
        entries: Vec<(Vec<Value>, Value)>,
    },
}

/// Whether `sort` has no lossless `u128` scalar code and therefore requires the
/// [`FuncStorage::FullValue`] path in function interpretations.
fn needs_value_storage(sort: Sort) -> bool {
    match sort {
        Sort::Float { exp, sig } => exp + sig > 128,
        Sort::BitVec(129..)
        | Sort::Int
        | Sort::Real
        | Sort::Array { .. }
        | Sort::Datatype(_)
        | Sort::Seq(_) => true,
        Sort::Bool | Sort::BitVec(_) | Sort::RoundingMode | Sort::Uninterpreted(_) => false,
    }
}

impl FuncValue {
    /// Whether any parameter or the result sort needs full-[`Value`] storage
    /// rather than the compact `u128` scalar path.
    pub fn uses_value_storage_for(params: &[Sort], result: Sort) -> bool {
        params.iter().copied().any(needs_value_storage) || needs_value_storage(result)
    }

    /// Creates a constant scalar function mapping every argument tuple to
    /// `default`.
    ///
    /// # Panics
    ///
    /// Panics if any parameter or the result sort requires full [`Value`]
    /// storage (wide `BitVec`/`Float`, `Int`/`Real`/array/datatype) — those
    /// interpretations must use [`FuncValue::constant_value`].
    pub fn constant(params: Vec<Sort>, result: Sort, default: u128) -> Self {
        assert!(
            !Self::uses_value_storage_for(&params, result),
            "function arguments/result require full-value storage; use FuncValue::constant_value"
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

    /// Creates a constant full-value function mapping every argument tuple to
    /// `default`. The default is any value of the result sort; the original
    /// query only constrains the explicitly defined points.
    ///
    /// # Panics
    ///
    /// Panics if neither a parameter nor the result requires full [`Value`]
    /// storage (use [`FuncValue::constant`] for purely scalar functions), or if
    /// `default`'s sort does not match `result`.
    pub fn constant_value(params: Vec<Sort>, result: Sort, default: Value) -> Self {
        assert!(
            Self::uses_value_storage_for(&params, result),
            "FuncValue::constant_value is for full-value-storage functions"
        );
        assert!(
            value_matches_sort(&default, result),
            "default value sort must match the function result sort"
        );
        let default = canonicalize_for_sort(result, default);
        Self {
            storage: FuncStorage::FullValue {
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

    /// Whether this interpretation uses the full-[`Value`]-keyed storage path.
    pub fn uses_value_storage(&self) -> bool {
        matches!(self.storage, FuncStorage::FullValue { .. })
    }

    /// Legacy name for [`Self::uses_value_storage`].
    pub fn is_arith(&self) -> bool {
        self.uses_value_storage()
    }

    /// The encoded result for `args` (each argument encoded to `u128`).
    ///
    /// # Panics
    ///
    /// Panics if `args` does not match the declared arity, or if this is a
    /// full-value-storage interpretation (use [`FuncValue::apply_value`]).
    pub fn apply(&self, args: &[u128]) -> u128 {
        match &self.storage {
            FuncStorage::Scalar { default, entries } => {
                let key = self.normalize_key(args);
                entries.get(&key).copied().unwrap_or(*default)
            }
            FuncStorage::FullValue { .. } => {
                panic!("FuncValue::apply on a full-value-storage function (use apply_value)")
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
            FuncStorage::FullValue { default, entries } => {
                let key: Vec<Value> = self
                    .params
                    .iter()
                    .copied()
                    .zip(args.iter().cloned())
                    .map(|(sort, value)| canonicalize_for_sort(sort, value))
                    .collect();
                canonicalize_for_sort(
                    self.result,
                    entries
                        .iter()
                        .find(|(k, _)| *k == key)
                        .map_or_else(|| default.clone(), |(_, v)| v.clone()),
                )
            }
        }
    }

    /// Returns a copy of this scalar function with `args` mapped to `result`.
    ///
    /// # Panics
    ///
    /// Panics if `args` does not match the declared arity, or if this is a
    /// full-value-storage interpretation (use [`FuncValue::define_value`]).
    #[must_use]
    pub fn define(&self, args: &[u128], result: u128) -> Self {
        let FuncStorage::Scalar { default, entries } = &self.storage else {
            panic!("FuncValue::define on a full-value-storage function (use define_value)");
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

    /// Returns a copy of this full-value function with the `args` tuple mapped to
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
        let FuncStorage::FullValue { default, entries } = &self.storage else {
            panic!("FuncValue::define_value on a scalar-storage function (use define)");
        };
        assert_eq!(args.len(), self.params.len(), "function arity mismatch");
        for (&sort, arg) in self.params.iter().zip(args) {
            assert!(
                value_matches_sort(arg, sort),
                "argument sort must match the parameter sort"
            );
        }
        assert!(
            value_matches_sort(&result, self.result),
            "result sort must match the function result sort"
        );
        let key: Vec<Value> = self
            .params
            .iter()
            .copied()
            .zip(args.iter().cloned())
            .map(|(sort, value)| canonicalize_for_sort(sort, value))
            .collect();
        let result = canonicalize_for_sort(self.result, result);
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
            storage: FuncStorage::FullValue {
                default: default.clone(),
                entries,
            },
        }
    }

    /// The default (encoded) result value (scalar storage).
    ///
    /// # Panics
    ///
    /// Panics for a full-value-storage interpretation (use
    /// [`FuncValue::default_value`]).
    pub fn default_result(&self) -> u128 {
        match &self.storage {
            FuncStorage::Scalar { default, .. } => *default,
            FuncStorage::FullValue { .. } => {
                panic!("FuncValue::default_result on a full-value-storage function")
            }
        }
    }

    /// The default result [`Value`] (works for both storage modes).
    pub fn default_value(&self) -> Value {
        match &self.storage {
            FuncStorage::Scalar { default, .. } => Value::from_scalar_code(self.result, *default),
            FuncStorage::FullValue { default, .. } => default.clone(),
        }
    }

    /// The overriding `(args, result)` entries in argument-tuple order (scalar
    /// storage only).
    ///
    /// # Panics
    ///
    /// Panics for a full-value-storage interpretation (use
    /// [`FuncValue::value_entries`]).
    pub fn entries(&self) -> impl Iterator<Item = (&[u128], u128)> + '_ {
        let FuncStorage::Scalar { entries, .. } = &self.storage else {
            panic!("FuncValue::entries on a full-value-storage function (use value_entries)");
        };
        entries.iter().map(|(k, &v)| (k.as_slice(), v))
    }

    /// The overriding `(args, result)` entries as full [`Value`]s, in definition
    /// order (full-value storage only).
    pub fn value_entries(&self) -> impl Iterator<Item = (&[Value], &Value)> + '_ {
        let entries: &[(Vec<Value>, Value)] = match &self.storage {
            FuncStorage::FullValue { entries, .. } => entries,
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
        Sort::RoundingMode => canonical_rounding_mode(value),
        Sort::Float { exp, sig } => canonical_float_u128(exp, sig, value),
        Sort::Uninterpreted(_) => value,
        Sort::Array { .. } => panic!("scalar encoding of an array sort"),
        Sort::Int => panic!("scalar encoding of an integer sort"),
        Sort::Real => panic!("scalar encoding of a real sort"),
        Sort::Datatype(_) => panic!("scalar encoding of a datatype sort"),
        // TODO(P2.7 A.1b): Seq handling. Mirrors the non-scalar sibling guards:
        // a sequence is not a `u128` scalar (needs_value_storage(Seq) == true),
        // so it is routed through FullValue and never reaches this scalar helper.
        Sort::Seq(_) => panic!("scalar encoding of a sequence sort"),
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
            Sort::BitVec(w) if w > 128 => Value::WideBv(crate::wide::WideUint::from_u128(code, w)),
            Sort::BitVec(w) => Value::Bv {
                width: w,
                value: code & mask(w),
            },
            Sort::RoundingMode => Value::Bv {
                width: 3,
                value: canonical_rounding_mode(code),
            },
            // Float values use one canonical representative for SMT-LIB's
            // single NaN theory value.
            Sort::Float { exp, sig } => Value::Bv {
                width: exp + sig,
                value: canonical_float_u128(exp, sig, code),
            },
            Sort::Uninterpreted(sort) => Value::Uninterpreted { sort, value: code },
            Sort::Array { .. } => panic!("scalar decoding of an array sort"),
            Sort::Int => panic!("scalar decoding of an integer sort"),
            // A real sort never decodes from a scalar code (real values — rational
            // or algebraic — are not scalar bit patterns).
            Sort::Real => panic!("scalar decoding of a real sort"),
            Sort::Datatype(_) => panic!("scalar decoding of a datatype sort"),
            // TODO(P2.7 A.1b): Seq handling. Mirrors the non-scalar sibling
            // guards: a sequence is not a `u128` scalar code
            // (needs_value_storage(Seq) == true), so it is stored via FullValue
            // and never decoded through this scalar helper.
            Sort::Seq(_) => panic!("scalar decoding of a sequence sort"),
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
            Value::Bv { value, .. } | Value::Uninterpreted { value, .. } => *value,
            Value::WideBv(_) => panic!("scalar encoding of a >128-bit bit-vector value"),
            Value::Array(_) | Value::GenericArray(_) => {
                panic!("scalar encoding of an array value")
            }
            Value::Int(_) => panic!("scalar encoding of an integer value"),
            Value::Real(_) => panic!("scalar encoding of a real value"),
            Value::RealAlgebraic(_) => panic!("scalar encoding of a real-algebraic value"),
            Value::Datatype { .. } => panic!("scalar encoding of a datatype value"),
            // A sequence is not a `u128` scalar (it routes through FullValue
            // storage, like arrays); mirror the array/datatype sibling guards.
            Value::Seq(_) => panic!("scalar encoding of a sequence value"),
        }
    }

    /// The sort of this value.
    ///
    /// A [`Value::Seq`] recovers its element key from its first element. An
    /// **empty** sequence carries no element (the value shape is `Seq(Vec)`), so
    /// its element sort cannot be recovered here; the documented fallback is the
    /// `String` element (`BitVec(18)`). This is only a fallback — the evaluator
    /// always knows an empty sequence's true sort from the term's
    /// [`crate::Op::SeqEmpty`] element key, so this path is not load-bearing for
    /// well-sorted evaluation.
    // TODO(P2.7): if empty non-string sequences need a precise value-level sort,
    // carry the element `ArraySortKey` in `Value::Seq` (superseding ADR).
    pub fn sort(&self) -> Sort {
        match self {
            Value::Bool(_) => Sort::Bool,
            Value::Bv { width, .. } => Sort::BitVec(*width),
            Value::WideBv(w) => Sort::BitVec(w.width()),
            Value::Array(array) => Sort::Array {
                index: ArraySortKey::BitVec(array.index_width),
                element: ArraySortKey::BitVec(array.element_width),
            },
            Value::GenericArray(array) => Sort::Array {
                index: array.index_sort(),
                element: array.element_sort(),
            },
            Value::Int(_) => Sort::Int,
            Value::Real(_) | Value::RealAlgebraic(_) => Sort::Real,
            Value::Datatype { datatype, .. } => Sort::Datatype(*datatype),
            Value::Uninterpreted { sort, .. } => Sort::Uninterpreted(*sort),
            Value::Seq(elements) => {
                let element = elements
                    .first()
                    .and_then(|e| ArraySortKey::from_sort(e.sort()))
                    .unwrap_or(ArraySortKey::BitVec(Sort::STRING_ELEM_WIDTH));
                Sort::Seq(element)
            }
        }
    }

    /// Returns the Boolean payload, or `None` for non-Boolean values.
    pub fn as_bool(&self) -> Option<bool> {
        match self {
            Value::Bool(b) => Some(*b),
            Value::Bv { .. }
            | Value::Array(_)
            | Value::GenericArray(_)
            | Value::Int(_)
            | Value::Real(_)
            | Value::RealAlgebraic(_)
            | Value::Datatype { .. }
            | Value::Uninterpreted { .. }
            | Value::WideBv(_)
            | Value::Seq(_) => None,
        }
    }

    /// Returns the bit-vector payload `(width, value)`, or `None`.
    pub fn as_bv(&self) -> Option<(u32, u128)> {
        match self {
            Value::Bv { width, value } => Some((*width, *value)),
            Value::Bool(_)
            | Value::Array(_)
            | Value::GenericArray(_)
            | Value::Int(_)
            | Value::Real(_)
            | Value::RealAlgebraic(_)
            | Value::Datatype { .. }
            | Value::Uninterpreted { .. }
            | Value::WideBv(_)
            | Value::Seq(_) => None,
        }
    }

    /// Returns the bit-vector array payload, or `None` for non-BV-array values.
    pub fn as_array(&self) -> Option<&ArrayValue> {
        match self {
            Value::Array(array) => Some(array),
            Value::Bool(_)
            | Value::Bv { .. }
            | Value::GenericArray(_)
            | Value::Int(_)
            | Value::Real(_)
            | Value::RealAlgebraic(_)
            | Value::Datatype { .. }
            | Value::Uninterpreted { .. }
            | Value::WideBv(_)
            | Value::Seq(_) => None,
        }
    }

    /// Returns the generic array payload, or `None` for non-generic-array
    /// values.
    pub fn as_generic_array(&self) -> Option<&GenericArrayValue> {
        match self {
            Value::GenericArray(array) => Some(array),
            Value::Bool(_)
            | Value::Bv { .. }
            | Value::Array(_)
            | Value::Int(_)
            | Value::Real(_)
            | Value::RealAlgebraic(_)
            | Value::Datatype { .. }
            | Value::Uninterpreted { .. }
            | Value::WideBv(_)
            | Value::Seq(_) => None,
        }
    }

    /// Returns the integer payload, or `None` for non-integer values.
    pub fn as_int(&self) -> Option<i128> {
        match self {
            Value::Int(value) => Some(*value),
            Value::Bool(_)
            | Value::Bv { .. }
            | Value::Array(_)
            | Value::GenericArray(_)
            | Value::Real(_)
            | Value::RealAlgebraic(_)
            | Value::Datatype { .. }
            | Value::Uninterpreted { .. }
            | Value::WideBv(_)
            | Value::Seq(_) => None,
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
            | Value::GenericArray(_)
            | Value::Int(_)
            | Value::RealAlgebraic(_)
            | Value::Datatype { .. }
            | Value::Uninterpreted { .. }
            | Value::WideBv(_)
            | Value::Seq(_) => None,
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

/// Whether `value` is a concrete representation accepted for `sort`.
/// Float values deliberately reuse the BV value variants, so their format is
/// supplied by the owning term/signature rather than recovered from `Value`.
pub(crate) fn value_matches_sort(value: &Value, sort: Sort) -> bool {
    match (sort, value) {
        (Sort::RoundingMode, Value::Bv { width: 3, .. }) => true,
        (Sort::Float { exp, sig }, Value::Bv { width, .. }) => *width == exp + sig,
        (Sort::Float { exp, sig }, Value::WideBv(bits)) => bits.width() == exp + sig,
        _ => value.sort() == sort,
    }
}

/// Returns the canonical concrete representative of a value at `sort`.
/// Currently only Float has a quotient representation: all NaN interchange
/// encodings denote the same SMT-LIB value and become one positive quiet NaN.
pub(crate) fn canonicalize_for_sort(sort: Sort, value: Value) -> Value {
    if sort == Sort::RoundingMode {
        return match value {
            Value::Bv { value, .. } => Value::Bv {
                width: 3,
                value: canonical_rounding_mode(value),
            },
            other => other,
        };
    }
    let Sort::Float { exp, sig } = sort else {
        return value;
    };
    let width = exp + sig;
    match value {
        Value::Bv { value, .. } if width <= 128 => Value::Bv {
            width,
            value: canonical_float_u128(exp, sig, value),
        },
        Value::WideBv(bits) if bits.width() == width => {
            Value::WideBv(canonical_float_wide(exp, sig, &bits))
        }
        other => other,
    }
}

fn canonical_rounding_mode(value: u128) -> u128 {
    match value & 0b111 {
        0..=4 => value & 0b111,
        _ => 4,
    }
}

fn canonical_float_u128(exp: u32, sig: u32, value: u128) -> u128 {
    let width = exp + sig;
    debug_assert!(width <= 128 && exp > 1 && sig > 1);
    let value = value & mask(width);
    let fraction_width = sig - 1;
    let exponent = (value >> fraction_width) & mask(exp);
    let fraction = value & mask(fraction_width);
    if exponent == mask(exp) && fraction != 0 {
        (mask(exp) << fraction_width) | (1u128 << (fraction_width - 1))
    } else {
        value
    }
}

fn canonical_float_wide(
    exp: u32,
    sig: u32,
    value: &crate::wide::WideUint,
) -> crate::wide::WideUint {
    let fraction_width = sig - 1;
    let exponent_all_ones = (fraction_width..fraction_width + exp).all(|bit| value.bit(bit));
    let fraction_nonzero = (0..fraction_width).any(|bit| value.bit(bit));
    if !exponent_all_ones || !fraction_nonzero {
        return value.clone();
    }
    let mut bits = vec![false; (exp + sig) as usize];
    bits[(fraction_width - 1) as usize] = true;
    for bit in fraction_width..fraction_width + exp {
        bits[bit as usize] = true;
    }
    crate::wide::WideUint::from_lsb_bits(&bits)
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
            Value::GenericArray(array) => {
                write!(f, "(array default {}", array.default_value())?;
                for (index, element) in array.entries() {
                    write!(f, " [{index} -> {element}]")?;
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
            Value::Uninterpreted { sort, value } => write!(f, "@u{}:{value}", sort.index()),
            Value::Seq(elements) => {
                write!(f, "(seq")?;
                for element in elements {
                    write!(f, " {element}")?;
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
