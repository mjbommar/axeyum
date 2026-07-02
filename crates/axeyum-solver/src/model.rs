//! Models: satisfying assignments keyed by Axeyum symbols.

use axeyum_ir::{Assignment, FuncId, FuncValue, Rational, SymbolId, Value};

/// A satisfying assignment produced by a backend, keyed by Axeyum
/// [`SymbolId`]s — never by backend AST handles (backend-model note).
///
/// Entries are kept sorted by symbol ID so iteration order is deterministic.
/// Uninterpreted-function interpretations (ADR-0013), when present, are kept in
/// a separate list sorted by [`FuncId`].
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Model {
    entries: Vec<(SymbolId, Value)>,
    functions: Vec<(FuncId, FuncValue)>,
    /// Model-chosen interpretation of real division-by-zero, keyed by the
    /// numerator value (P2.5 free-division witnesses). SMT-LIB leaves real
    /// `(/ x 0)` unspecified; the solver's chosen value for each forced `x/0` is
    /// carried here so the `sat` replay (which re-evaluates the original
    /// division term) accepts the witness. Kept sorted by numerator for
    /// deterministic iteration; an empty map is exactly the total `x/0 = 0`
    /// evaluator convention. Mirrors [`Assignment::set_real_div_zero`].
    real_div_zero: Vec<(Rational, Rational)>,
}

impl Model {
    /// Creates an empty model.
    pub fn new() -> Self {
        Self::default()
    }

    /// Inserts or replaces the value for `symbol`.
    pub fn set(&mut self, symbol: SymbolId, value: Value) {
        match self.entries.binary_search_by_key(&symbol, |&(s, _)| s) {
            Ok(i) => self.entries[i].1 = value,
            Err(i) => self.entries.insert(i, (symbol, value)),
        }
    }

    /// The value assigned to `symbol`, if present.
    pub fn get(&self, symbol: SymbolId) -> Option<Value> {
        self.entries
            .binary_search_by_key(&symbol, |(s, _)| *s)
            .ok()
            .map(|i| self.entries[i].1.clone())
    }

    /// Iterates over `(symbol, value)` pairs in symbol order.
    pub fn iter(&self) -> impl Iterator<Item = (SymbolId, Value)> + '_ {
        self.entries.iter().cloned()
    }

    /// Inserts or replaces the interpretation for uninterpreted function
    /// `func` (ADR-0013).
    pub fn set_function(&mut self, func: FuncId, value: FuncValue) {
        match self.functions.binary_search_by_key(&func, |(f, _)| *f) {
            Ok(i) => self.functions[i].1 = value,
            Err(i) => self.functions.insert(i, (func, value)),
        }
    }

    /// The interpretation assigned to `func`, if present.
    pub fn function(&self, func: FuncId) -> Option<&FuncValue> {
        self.functions
            .binary_search_by_key(&func, |(f, _)| *f)
            .ok()
            .map(|i| &self.functions[i].1)
    }

    /// Iterates over `(func, interpretation)` pairs in function order.
    pub fn functions(&self) -> impl Iterator<Item = (FuncId, &FuncValue)> + '_ {
        self.functions.iter().map(|(f, v)| (*f, v))
    }

    /// Records the model-chosen value of `(/ numerator 0)` (P2.5 free-division
    /// witness), replacing any previous entry for the same numerator. Entries
    /// are kept in a deterministic, overflow-free order (lexicographic on the
    /// normalized `(numerator, denominator)` representation — a stable total
    /// order, not the numeric one, which suffices for reproducible output and
    /// avoids the `Rational` `Ord` overflow panic on large model values).
    pub fn set_real_div_zero(&mut self, numerator: Rational, quotient: Rational) {
        match self
            .real_div_zero
            .binary_search_by_key(&div_zero_key(numerator), |&(n, _)| div_zero_key(n))
        {
            Ok(i) => self.real_div_zero[i].1 = quotient,
            Err(i) => self.real_div_zero.insert(i, (numerator, quotient)),
        }
    }

    /// The model-chosen value of `(/ numerator 0)`, if the model fixes one.
    pub fn real_div_zero(&self, numerator: Rational) -> Option<Rational> {
        self.real_div_zero
            .binary_search_by_key(&div_zero_key(numerator), |&(n, _)| div_zero_key(n))
            .ok()
            .map(|i| self.real_div_zero[i].1)
    }

    /// Iterates over the recorded real division-by-zero interpretations
    /// (`numerator -> quotient`) in the deterministic key order.
    pub fn real_div_zeros(&self) -> impl Iterator<Item = (Rational, Rational)> + '_ {
        self.real_div_zero.iter().copied()
    }

    /// Number of assigned symbols.
    pub fn len(&self) -> usize {
        self.entries.len()
    }

    /// Returns `true` if the model assigns no symbols.
    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    /// Converts to an evaluator [`Assignment`] for check-by-evaluation —
    /// the level-1 evidence check (evidence-and-checking note).
    pub fn to_assignment(&self) -> Assignment {
        let mut asg = Assignment::new();
        for (s, v) in self.iter() {
            asg.set(s, v);
        }
        for (f, v) in &self.functions {
            asg.set_function(*f, v.clone());
        }
        for &(n, q) in &self.real_div_zero {
            asg.set_real_div_zero(n, q);
        }
        asg
    }
}

/// A deterministic, overflow-free sort key for a `Rational`: the lexicographic
/// pair of its normalized numerator and denominator. This is a stable total
/// order (distinct rationals get distinct keys because the representation is in
/// lowest terms with a positive denominator), used only to order the
/// division-by-zero entries reproducibly — it deliberately avoids the numeric
/// `Rational` `Ord`, which cross-multiplies and can overflow-panic on the large
/// values a model may assign.
fn div_zero_key(r: Rational) -> (i128, i128) {
    (r.numerator(), r.denominator())
}
