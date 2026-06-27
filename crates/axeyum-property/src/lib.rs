//! Typed prove-or-counterexample SDK over Axeyum evidence.
//!
//! This crate is a thin consumer-facing wrapper. It builds terms in an
//! [`axeyum_ir::TermArena`], then delegates proving to
//! [`axeyum_solver::prove`] or [`axeyum_solver::prove_minimized`]. It does not
//! add solver logic or weaken the underlying evidence contract.

use axeyum_ir::{IrError, Sort, SymbolId, TermArena, TermId, Value};
use axeyum_solver::{Model, ProofOutcome, SolverConfig, SolverError, prove, prove_minimized};

/// Errors produced by the property SDK.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PropertyError {
    /// Term construction failed.
    Ir(IrError),
    /// Solving or evidence production failed.
    Solver(SolverError),
    /// A model value had the wrong sort for the typed handle used to read it.
    ModelSortMismatch {
        /// The symbol whose value was being lifted.
        symbol: SymbolId,
        /// The value found in the model.
        value: Value,
    },
    /// A model value cannot be rendered as a native Rust literal by this SDK
    /// layer.
    UnsupportedRustLiteral {
        /// The original Axeyum symbol name.
        name: String,
        /// The value that could not be rendered.
        value: Value,
    },
}

impl core::fmt::Display for PropertyError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            PropertyError::Ir(error) => write!(f, "{error}"),
            PropertyError::Solver(error) => write!(f, "{error}"),
            PropertyError::ModelSortMismatch { symbol, value } => write!(
                f,
                "model value for symbol #{} has the wrong sort: {value:?}",
                symbol.index()
            ),
            PropertyError::UnsupportedRustLiteral { name, value } => {
                write!(
                    f,
                    "cannot render counterexample input `{name}` with value {value:?} as a native Rust literal"
                )
            }
        }
    }
}

impl std::error::Error for PropertyError {}

impl From<IrError> for PropertyError {
    fn from(error: IrError) -> Self {
        Self::Ir(error)
    }
}

impl From<SolverError> for PropertyError {
    fn from(error: SolverError) -> Self {
        Self::Solver(error)
    }
}

/// One scalar input binding from a replay-checked counterexample model.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InputBinding {
    symbol: SymbolId,
    name: String,
    rust_ident: String,
    sort: Sort,
    value: Value,
}

impl InputBinding {
    /// The Axeyum symbol ID.
    #[must_use]
    pub fn symbol(&self) -> SymbolId {
        self.symbol
    }

    /// The original Axeyum symbol name.
    #[must_use]
    pub fn name(&self) -> &str {
        &self.name
    }

    /// A deterministic Rust-safe identifier derived from [`Self::name`].
    #[must_use]
    pub fn rust_ident(&self) -> &str {
        &self.rust_ident
    }

    /// The declared sort.
    #[must_use]
    pub fn sort(&self) -> Sort {
        self.sort
    }

    /// The model value.
    #[must_use]
    pub fn value(&self) -> &Value {
        &self.value
    }

    /// Renders this binding as a Rust `let` statement.
    ///
    /// # Errors
    ///
    /// Returns [`PropertyError::UnsupportedRustLiteral`] for values outside the
    /// native scalar surface: Bool, Int, and BV widths up to 128 bits.
    pub fn render_rust_let(&self) -> Result<String, PropertyError> {
        match &self.value {
            Value::Bool(value) => Ok(format!("let {}: bool = {value};", self.rust_ident)),
            Value::Int(value) => Ok(format!(
                "let {}: i128 = {};",
                self.rust_ident,
                render_i128_literal(*value)
            )),
            Value::Bv { width, value } => Ok(format!(
                "let {}: {} = {}; // BV{}",
                self.rust_ident,
                rust_uint_type(*width),
                render_uint_literal(*width, *value),
                width
            )),
            Value::WideBv(_)
            | Value::Array(_)
            | Value::GenericArray(_)
            | Value::Real(_)
            | Value::RealAlgebraic(_)
            | Value::Datatype { .. }
            | Value::Uninterpreted { .. } => Err(PropertyError::UnsupportedRustLiteral {
                name: self.name.clone(),
                value: self.value.clone(),
            }),
        }
    }
}

/// A deterministic view of a disproving model over SDK-declared inputs.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Counterexample {
    bindings: Vec<InputBinding>,
}

impl Counterexample {
    /// Creates a counterexample from already-normalized bindings.
    #[must_use]
    pub fn new(bindings: Vec<InputBinding>) -> Self {
        Self { bindings }
    }

    /// The input bindings in SDK declaration order.
    #[must_use]
    pub fn bindings(&self) -> &[InputBinding] {
        &self.bindings
    }

    /// Renders all bindings as Rust `let` statements.
    ///
    /// # Errors
    ///
    /// Returns [`PropertyError::UnsupportedRustLiteral`] if any binding is not
    /// representable by a native Rust scalar literal.
    pub fn render_rust_let_bindings(&self) -> Result<String, PropertyError> {
        let mut out = String::new();
        for binding in &self.bindings {
            out.push_str(&binding.render_rust_let()?);
            out.push('\n');
        }
        Ok(out)
    }

    /// Renders a complete Rust `#[test]` skeleton.
    ///
    /// `body` is inserted after the generated input bindings and should contain
    /// the caller's domain replay/assertion code. This function intentionally
    /// does not invent replay semantics; it only makes the model values
    /// reproducible in Rust syntax.
    ///
    /// # Errors
    ///
    /// Returns [`PropertyError::UnsupportedRustLiteral`] if any binding is not
    /// representable by a native Rust scalar literal.
    pub fn render_rust_test(&self, test_name: &str, body: &str) -> Result<String, PropertyError> {
        let mut out = String::new();
        out.push_str("#[test]\n");
        out.push_str("fn ");
        out.push_str(&sanitize_rust_ident(test_name));
        out.push_str("() {\n");
        for binding in &self.bindings {
            out.push_str("    ");
            out.push_str(&binding.render_rust_let()?);
            out.push('\n');
        }
        for line in body.lines() {
            if line.is_empty() {
                out.push('\n');
            } else {
                out.push_str("    ");
                out.push_str(line);
                out.push('\n');
            }
        }
        out.push_str("}\n");
        Ok(out)
    }
}

/// A typed property-building context.
#[derive(Debug, Clone)]
pub struct Property {
    arena: TermArena,
    hypotheses: Vec<TermId>,
    counterexample_symbols: Vec<SymbolId>,
    config: SolverConfig,
}

impl Default for Property {
    fn default() -> Self {
        Self::new()
    }
}

impl Property {
    /// Creates an empty property context with the default solver configuration.
    #[must_use]
    pub fn new() -> Self {
        Self {
            arena: TermArena::new(),
            hypotheses: Vec::new(),
            counterexample_symbols: Vec::new(),
            config: SolverConfig::default(),
        }
    }

    /// Creates an empty property context with an explicit solver configuration.
    #[must_use]
    pub fn with_config(config: SolverConfig) -> Self {
        Self {
            config,
            ..Self::new()
        }
    }

    /// The underlying term arena.
    #[must_use]
    pub fn arena(&self) -> &TermArena {
        &self.arena
    }

    /// The underlying term arena, for advanced term construction.
    pub fn arena_mut(&mut self) -> &mut TermArena {
        &mut self.arena
    }

    /// The solver configuration used by future proof calls.
    #[must_use]
    pub fn config(&self) -> &SolverConfig {
        &self.config
    }

    /// Mutates the solver configuration used by future proof calls.
    pub fn config_mut(&mut self) -> &mut SolverConfig {
        &mut self.config
    }

    /// Declares a Boolean input symbol and includes it in minimization order.
    ///
    /// # Errors
    ///
    /// Returns [`PropertyError`] if the symbol name conflicts with an existing
    /// declaration.
    pub fn bool(&mut self, name: &str) -> Result<Bool, PropertyError> {
        let symbol = self.arena.declare(name, Sort::Bool)?;
        let term = self.arena.var(symbol);
        self.track_symbol(symbol);
        Ok(Bool {
            term,
            symbol: Some(symbol),
        })
    }

    /// Declares a bit-vector input symbol and includes it in minimization order.
    ///
    /// # Errors
    ///
    /// Returns [`PropertyError`] if `W` is not a valid bit-vector width or the
    /// symbol name conflicts with an existing declaration.
    pub fn bv<const W: u32>(&mut self, name: &str) -> Result<Bv<W>, PropertyError> {
        let symbol = self.arena.declare(name, Sort::BitVec(W))?;
        let term = self.arena.var(symbol);
        self.track_symbol(symbol);
        Ok(Bv {
            term,
            symbol: Some(symbol),
        })
    }

    /// Declares an integer input symbol and includes it in minimization order.
    ///
    /// # Errors
    ///
    /// Returns [`PropertyError`] if the symbol name conflicts with an existing
    /// declaration.
    pub fn int(&mut self, name: &str) -> Result<Int, PropertyError> {
        let symbol = self.arena.declare(name, Sort::Int)?;
        let term = self.arena.var(symbol);
        self.track_symbol(symbol);
        Ok(Int {
            term,
            symbol: Some(symbol),
        })
    }

    /// Creates a Boolean constant.
    pub fn bool_const(&mut self, value: bool) -> Bool {
        Bool {
            term: self.arena.bool_const(value),
            symbol: None,
        }
    }

    /// Creates a bit-vector constant.
    ///
    /// # Errors
    ///
    /// Returns [`PropertyError`] if `W` is invalid or `value` does not fit.
    pub fn bv_const<const W: u32>(&mut self, value: u128) -> Result<Bv<W>, PropertyError> {
        Ok(Bv {
            term: self.arena.bv_const(W, value)?,
            symbol: None,
        })
    }

    /// Creates an integer constant.
    pub fn int_const(&mut self, value: i128) -> Int {
        Int {
            term: self.arena.int_const(value),
            symbol: None,
        }
    }

    /// Adds a hypothesis that must hold for the property.
    pub fn assume(&mut self, condition: Bool) {
        self.hypotheses.push(condition.term);
    }

    /// The current hypotheses as raw terms.
    #[must_use]
    pub fn hypotheses(&self) -> &[TermId] {
        &self.hypotheses
    }

    /// Symbols used as lexicographic objectives for minimized counterexamples.
    #[must_use]
    pub fn counterexample_symbols(&self) -> &[SymbolId] {
        &self.counterexample_symbols
    }

    /// Proves `goal` from the current hypotheses.
    ///
    /// # Errors
    ///
    /// Returns [`PropertyError`] if evidence production fails or the underlying
    /// solver reports a construction error.
    pub fn prove(&mut self, goal: Bool) -> Result<ProofOutcome, PropertyError> {
        Ok(prove(
            &mut self.arena,
            &self.hypotheses,
            goal.term,
            &self.config,
        )?)
    }

    /// Proves `goal`, minimizing a disproving model over declared SDK inputs.
    ///
    /// # Errors
    ///
    /// Returns [`PropertyError`] if evidence production, minimization, or term
    /// construction fails. Unsupported objective sorts are reported by the
    /// underlying solver; this v0 SDK tracks only Bool, BV, and Int symbols.
    pub fn prove_minimized(&mut self, goal: Bool) -> Result<ProofOutcome, PropertyError> {
        Ok(prove_minimized(
            &mut self.arena,
            &self.hypotheses,
            goal.term,
            &self.counterexample_symbols,
            &self.config,
        )?)
    }

    /// Extracts a deterministic counterexample view from a model.
    ///
    /// Only symbols declared through this SDK are included, and they are emitted
    /// in declaration order. Missing symbols are skipped; present values are
    /// checked against the arena declaration before being returned.
    ///
    /// # Errors
    ///
    /// Returns [`PropertyError::ModelSortMismatch`] if a model value does not
    /// match the symbol's declared sort.
    pub fn counterexample(&self, model: &Model) -> Result<Counterexample, PropertyError> {
        let mut used_idents = Vec::new();
        let mut bindings = Vec::new();
        for &symbol in &self.counterexample_symbols {
            let Some(value) = model.get(symbol) else {
                continue;
            };
            let (name, sort) = self.arena.symbol(symbol);
            if value.sort() != sort {
                return Err(PropertyError::ModelSortMismatch { symbol, value });
            }
            let rust_ident = unique_rust_ident(name, &mut used_idents);
            bindings.push(InputBinding {
                symbol,
                name: name.to_owned(),
                rust_ident,
                sort,
                value,
            });
        }
        Ok(Counterexample::new(bindings))
    }

    /// Extracts a counterexample when `outcome` is disproved.
    ///
    /// # Errors
    ///
    /// Returns [`PropertyError::ModelSortMismatch`] if a model value does not
    /// match the symbol's declared sort.
    pub fn counterexample_from_outcome(
        &self,
        outcome: &ProofOutcome,
    ) -> Result<Option<Counterexample>, PropertyError> {
        match outcome {
            ProofOutcome::Disproved(model) => Ok(Some(self.counterexample(model)?)),
            ProofOutcome::Proved(_) | ProofOutcome::Unknown(_) => Ok(None),
        }
    }

    fn track_symbol(&mut self, symbol: SymbolId) {
        if !self.counterexample_symbols.contains(&symbol) {
            self.counterexample_symbols.push(symbol);
        }
    }
}

/// Typed Boolean expression handle.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Bool {
    term: TermId,
    symbol: Option<SymbolId>,
}

impl Bool {
    /// The underlying term.
    #[must_use]
    pub fn term(self) -> TermId {
        self.term
    }

    /// The underlying input symbol, when this handle is a declared variable.
    #[must_use]
    pub fn symbol(self) -> Option<SymbolId> {
        self.symbol
    }

    /// Boolean negation.
    ///
    /// # Errors
    ///
    /// Returns [`PropertyError`] if term construction fails.
    pub fn not(self, property: &mut Property) -> Result<Self, PropertyError> {
        Ok(Self::expr(property.arena.not(self.term)?))
    }

    /// Boolean conjunction.
    ///
    /// # Errors
    ///
    /// Returns [`PropertyError`] if term construction fails.
    pub fn and(self, property: &mut Property, rhs: Self) -> Result<Self, PropertyError> {
        Ok(Self::expr(property.arena.and(self.term, rhs.term)?))
    }

    /// Boolean disjunction.
    ///
    /// # Errors
    ///
    /// Returns [`PropertyError`] if term construction fails.
    pub fn or(self, property: &mut Property, rhs: Self) -> Result<Self, PropertyError> {
        Ok(Self::expr(property.arena.or(self.term, rhs.term)?))
    }

    /// Boolean implication.
    ///
    /// # Errors
    ///
    /// Returns [`PropertyError`] if term construction fails.
    pub fn implies(self, property: &mut Property, rhs: Self) -> Result<Self, PropertyError> {
        Ok(Self::expr(property.arena.implies(self.term, rhs.term)?))
    }

    /// Boolean equality.
    ///
    /// # Errors
    ///
    /// Returns [`PropertyError`] if term construction fails.
    pub fn eq(self, property: &mut Property, rhs: Self) -> Result<Self, PropertyError> {
        Ok(Self::expr(property.arena.eq(self.term, rhs.term)?))
    }

    /// Reads this Boolean variable from a model.
    ///
    /// # Errors
    ///
    /// Returns [`PropertyError`] if a model entry exists but has the wrong sort.
    pub fn value(self, model: &Model) -> Result<Option<bool>, PropertyError> {
        let Some(symbol) = self.symbol else {
            return Ok(None);
        };
        match model.get(symbol) {
            Some(Value::Bool(value)) => Ok(Some(value)),
            Some(value) => Err(PropertyError::ModelSortMismatch { symbol, value }),
            None => Ok(None),
        }
    }

    fn expr(term: TermId) -> Self {
        Self { term, symbol: None }
    }
}

fn render_i128_literal(value: i128) -> String {
    if value == i128::MIN {
        "i128::MIN".to_owned()
    } else {
        format!("{value}_i128")
    }
}

fn render_uint_literal(width: u32, value: u128) -> String {
    let ty = rust_uint_type(width);
    let digits = usize::try_from(width.max(1).div_ceil(4)).expect("width fits usize");
    format!("0x{value:0>digits$x}_{ty}")
}

fn rust_uint_type(width: u32) -> &'static str {
    match width {
        0..=8 => "u8",
        9..=16 => "u16",
        17..=32 => "u32",
        33..=64 => "u64",
        _ => "u128",
    }
}

fn unique_rust_ident(name: &str, used: &mut Vec<String>) -> String {
    let base = sanitize_rust_ident(name);
    if !used.iter().any(|existing| existing == &base) {
        used.push(base.clone());
        return base;
    }
    for i in 1.. {
        let candidate = format!("{base}_{i}");
        if !used.iter().any(|existing| existing == &candidate) {
            used.push(candidate.clone());
            return candidate;
        }
    }
    unreachable!("unbounded suffix search always finds a fresh identifier")
}

fn sanitize_rust_ident(name: &str) -> String {
    let mut out = String::new();
    for (i, ch) in name.chars().enumerate() {
        let ok = ch == '_' || ch.is_ascii_alphanumeric();
        let ch = if ok { ch } else { '_' };
        if i == 0 && !(ch == '_' || ch.is_ascii_alphabetic()) {
            out.push('_');
        }
        out.push(ch);
    }
    if out.is_empty() || out == "_" {
        out.clear();
        out.push_str("input");
    }
    if is_rust_keyword(&out) {
        out.push('_');
    }
    out
}

fn is_rust_keyword(ident: &str) -> bool {
    matches!(
        ident,
        "as" | "break"
            | "const"
            | "continue"
            | "crate"
            | "else"
            | "enum"
            | "extern"
            | "false"
            | "fn"
            | "for"
            | "if"
            | "impl"
            | "in"
            | "let"
            | "loop"
            | "match"
            | "mod"
            | "move"
            | "mut"
            | "pub"
            | "ref"
            | "return"
            | "self"
            | "Self"
            | "static"
            | "struct"
            | "super"
            | "trait"
            | "true"
            | "type"
            | "unsafe"
            | "use"
            | "where"
            | "while"
            | "async"
            | "await"
            | "dyn"
            | "abstract"
            | "become"
            | "box"
            | "do"
            | "final"
            | "macro"
            | "override"
            | "priv"
            | "typeof"
            | "unsized"
            | "virtual"
            | "yield"
            | "try"
    )
}

/// Typed bit-vector expression handle.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Bv<const W: u32> {
    term: TermId,
    symbol: Option<SymbolId>,
}

impl<const W: u32> Bv<W> {
    /// The underlying term.
    #[must_use]
    pub fn term(self) -> TermId {
        self.term
    }

    /// The underlying input symbol, when this handle is a declared variable.
    #[must_use]
    pub fn symbol(self) -> Option<SymbolId> {
        self.symbol
    }

    /// Wrapping addition.
    ///
    /// # Errors
    ///
    /// Returns [`PropertyError`] if term construction fails.
    pub fn add(self, property: &mut Property, rhs: Self) -> Result<Self, PropertyError> {
        Ok(Self::expr(property.arena.bv_add(self.term, rhs.term)?))
    }

    /// Wrapping subtraction.
    ///
    /// # Errors
    ///
    /// Returns [`PropertyError`] if term construction fails.
    pub fn sub(self, property: &mut Property, rhs: Self) -> Result<Self, PropertyError> {
        Ok(Self::expr(property.arena.bv_sub(self.term, rhs.term)?))
    }

    /// Wrapping multiplication.
    ///
    /// # Errors
    ///
    /// Returns [`PropertyError`] if term construction fails.
    pub fn mul(self, property: &mut Property, rhs: Self) -> Result<Self, PropertyError> {
        Ok(Self::expr(property.arena.bv_mul(self.term, rhs.term)?))
    }

    /// Bitwise negation.
    ///
    /// # Errors
    ///
    /// Returns [`PropertyError`] if term construction fails.
    pub fn not(self, property: &mut Property) -> Result<Self, PropertyError> {
        Ok(Self::expr(property.arena.bv_not(self.term)?))
    }

    /// Bitwise conjunction.
    ///
    /// # Errors
    ///
    /// Returns [`PropertyError`] if term construction fails.
    pub fn and(self, property: &mut Property, rhs: Self) -> Result<Self, PropertyError> {
        Ok(Self::expr(property.arena.bv_and(self.term, rhs.term)?))
    }

    /// Bitwise disjunction.
    ///
    /// # Errors
    ///
    /// Returns [`PropertyError`] if term construction fails.
    pub fn or(self, property: &mut Property, rhs: Self) -> Result<Self, PropertyError> {
        Ok(Self::expr(property.arena.bv_or(self.term, rhs.term)?))
    }

    /// Bitwise exclusive-or.
    ///
    /// # Errors
    ///
    /// Returns [`PropertyError`] if term construction fails.
    pub fn xor(self, property: &mut Property, rhs: Self) -> Result<Self, PropertyError> {
        Ok(Self::expr(property.arena.bv_xor(self.term, rhs.term)?))
    }

    /// Equality comparison.
    ///
    /// # Errors
    ///
    /// Returns [`PropertyError`] if term construction fails.
    pub fn eq(self, property: &mut Property, rhs: Self) -> Result<Bool, PropertyError> {
        Ok(Bool::expr(property.arena.eq(self.term, rhs.term)?))
    }

    /// Unsigned less-than comparison.
    ///
    /// # Errors
    ///
    /// Returns [`PropertyError`] if term construction fails.
    pub fn ult(self, property: &mut Property, rhs: Self) -> Result<Bool, PropertyError> {
        Ok(Bool::expr(property.arena.bv_ult(self.term, rhs.term)?))
    }

    /// Unsigned less-or-equal comparison.
    ///
    /// # Errors
    ///
    /// Returns [`PropertyError`] if term construction fails.
    pub fn ule(self, property: &mut Property, rhs: Self) -> Result<Bool, PropertyError> {
        Ok(Bool::expr(property.arena.bv_ule(self.term, rhs.term)?))
    }

    /// Unsigned greater-than comparison.
    ///
    /// # Errors
    ///
    /// Returns [`PropertyError`] if term construction fails.
    pub fn ugt(self, property: &mut Property, rhs: Self) -> Result<Bool, PropertyError> {
        Ok(Bool::expr(property.arena.bv_ugt(self.term, rhs.term)?))
    }

    /// Unsigned greater-or-equal comparison.
    ///
    /// # Errors
    ///
    /// Returns [`PropertyError`] if term construction fails.
    pub fn uge(self, property: &mut Property, rhs: Self) -> Result<Bool, PropertyError> {
        Ok(Bool::expr(property.arena.bv_uge(self.term, rhs.term)?))
    }

    /// Signed less-than comparison.
    ///
    /// # Errors
    ///
    /// Returns [`PropertyError`] if term construction fails.
    pub fn slt(self, property: &mut Property, rhs: Self) -> Result<Bool, PropertyError> {
        Ok(Bool::expr(property.arena.bv_slt(self.term, rhs.term)?))
    }

    /// Signed less-or-equal comparison.
    ///
    /// # Errors
    ///
    /// Returns [`PropertyError`] if term construction fails.
    pub fn sle(self, property: &mut Property, rhs: Self) -> Result<Bool, PropertyError> {
        Ok(Bool::expr(property.arena.bv_sle(self.term, rhs.term)?))
    }

    /// Signed greater-than comparison.
    ///
    /// # Errors
    ///
    /// Returns [`PropertyError`] if term construction fails.
    pub fn sgt(self, property: &mut Property, rhs: Self) -> Result<Bool, PropertyError> {
        Ok(Bool::expr(property.arena.bv_sgt(self.term, rhs.term)?))
    }

    /// Signed greater-or-equal comparison.
    ///
    /// # Errors
    ///
    /// Returns [`PropertyError`] if term construction fails.
    pub fn sge(self, property: &mut Property, rhs: Self) -> Result<Bool, PropertyError> {
        Ok(Bool::expr(property.arena.bv_sge(self.term, rhs.term)?))
    }

    /// Unsigned addition overflow predicate.
    ///
    /// # Errors
    ///
    /// Returns [`PropertyError`] if term construction fails.
    pub fn uadd_overflows(self, property: &mut Property, rhs: Self) -> Result<Bool, PropertyError> {
        Ok(Bool::expr(property.arena.bv_uaddo(self.term, rhs.term)?))
    }

    /// Unsigned subtraction overflow/borrow predicate.
    ///
    /// # Errors
    ///
    /// Returns [`PropertyError`] if term construction fails.
    pub fn usub_overflows(self, property: &mut Property, rhs: Self) -> Result<Bool, PropertyError> {
        Ok(Bool::expr(property.arena.bv_usubo(self.term, rhs.term)?))
    }

    /// Unsigned multiplication overflow predicate.
    ///
    /// # Errors
    ///
    /// Returns [`PropertyError`] if term construction fails.
    pub fn umul_overflows(self, property: &mut Property, rhs: Self) -> Result<Bool, PropertyError> {
        Ok(Bool::expr(property.arena.bv_umulo(self.term, rhs.term)?))
    }

    /// Reads this bit-vector variable from a model as an Axeyum value.
    ///
    /// # Errors
    ///
    /// Returns [`PropertyError`] if a model entry exists but has the wrong
    /// bit-vector width or sort.
    pub fn value(self, model: &Model) -> Result<Option<Value>, PropertyError> {
        let Some(symbol) = self.symbol else {
            return Ok(None);
        };
        match model.get(symbol) {
            Some(value @ Value::Bv { width, .. }) if width == W => Ok(Some(value)),
            Some(value) if matches!(&value, Value::WideBv(wide) if wide.width() == W) => {
                Ok(Some(value))
            }
            Some(value) => Err(PropertyError::ModelSortMismatch { symbol, value }),
            None => Ok(None),
        }
    }

    /// Reads this bit-vector variable from a model as a `u128` when `W <= 128`.
    ///
    /// # Errors
    ///
    /// Returns [`PropertyError`] if a model entry exists but has the wrong sort.
    pub fn value_u128(self, model: &Model) -> Result<Option<u128>, PropertyError> {
        let Some(symbol) = self.symbol else {
            return Ok(None);
        };
        match model.get(symbol) {
            Some(Value::Bv { width, value }) if width == W => Ok(Some(value)),
            Some(value) => Err(PropertyError::ModelSortMismatch { symbol, value }),
            None => Ok(None),
        }
    }

    fn expr(term: TermId) -> Self {
        Self { term, symbol: None }
    }
}

/// Typed integer expression handle.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Int {
    term: TermId,
    symbol: Option<SymbolId>,
}

impl Int {
    /// The underlying term.
    #[must_use]
    pub fn term(self) -> TermId {
        self.term
    }

    /// The underlying input symbol, when this handle is a declared variable.
    #[must_use]
    pub fn symbol(self) -> Option<SymbolId> {
        self.symbol
    }

    /// Integer addition.
    ///
    /// # Errors
    ///
    /// Returns [`PropertyError`] if term construction fails.
    pub fn add(self, property: &mut Property, rhs: Self) -> Result<Self, PropertyError> {
        Ok(Self::expr(property.arena.int_add(self.term, rhs.term)?))
    }

    /// Integer subtraction.
    ///
    /// # Errors
    ///
    /// Returns [`PropertyError`] if term construction fails.
    pub fn sub(self, property: &mut Property, rhs: Self) -> Result<Self, PropertyError> {
        Ok(Self::expr(property.arena.int_sub(self.term, rhs.term)?))
    }

    /// Integer multiplication.
    ///
    /// # Errors
    ///
    /// Returns [`PropertyError`] if term construction fails.
    pub fn mul(self, property: &mut Property, rhs: Self) -> Result<Self, PropertyError> {
        Ok(Self::expr(property.arena.int_mul(self.term, rhs.term)?))
    }

    /// Equality comparison.
    ///
    /// # Errors
    ///
    /// Returns [`PropertyError`] if term construction fails.
    pub fn eq(self, property: &mut Property, rhs: Self) -> Result<Bool, PropertyError> {
        Ok(Bool::expr(property.arena.eq(self.term, rhs.term)?))
    }

    /// Less-than comparison.
    ///
    /// # Errors
    ///
    /// Returns [`PropertyError`] if term construction fails.
    pub fn lt(self, property: &mut Property, rhs: Self) -> Result<Bool, PropertyError> {
        Ok(Bool::expr(property.arena.int_lt(self.term, rhs.term)?))
    }

    /// Less-or-equal comparison.
    ///
    /// # Errors
    ///
    /// Returns [`PropertyError`] if term construction fails.
    pub fn le(self, property: &mut Property, rhs: Self) -> Result<Bool, PropertyError> {
        Ok(Bool::expr(property.arena.int_le(self.term, rhs.term)?))
    }

    /// Greater-than comparison.
    ///
    /// # Errors
    ///
    /// Returns [`PropertyError`] if term construction fails.
    pub fn gt(self, property: &mut Property, rhs: Self) -> Result<Bool, PropertyError> {
        Ok(Bool::expr(property.arena.int_gt(self.term, rhs.term)?))
    }

    /// Greater-or-equal comparison.
    ///
    /// # Errors
    ///
    /// Returns [`PropertyError`] if term construction fails.
    pub fn ge(self, property: &mut Property, rhs: Self) -> Result<Bool, PropertyError> {
        Ok(Bool::expr(property.arena.int_ge(self.term, rhs.term)?))
    }

    /// Reads this integer variable from a model.
    ///
    /// # Errors
    ///
    /// Returns [`PropertyError`] if a model entry exists but has the wrong sort.
    pub fn value(self, model: &Model) -> Result<Option<i128>, PropertyError> {
        let Some(symbol) = self.symbol else {
            return Ok(None);
        };
        match model.get(symbol) {
            Some(Value::Int(value)) => Ok(Some(value)),
            Some(value) => Err(PropertyError::ModelSortMismatch { symbol, value }),
            None => Ok(None),
        }
    }

    fn expr(term: TermId) -> Self {
        Self { term, symbol: None }
    }
}
