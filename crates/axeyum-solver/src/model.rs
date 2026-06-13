//! Models: satisfying assignments keyed by Axeyum symbols.

use axeyum_ir::{Assignment, FuncId, FuncValue, SymbolId, Value};

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
        asg
    }
}
